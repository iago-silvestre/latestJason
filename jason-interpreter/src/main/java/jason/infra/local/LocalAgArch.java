package jason.infra.local;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.logging.Level;
import java.util.logging.Logger;

import jason.JasonException;
import jason.ReceiverNotFoundException;
import jason.architecture.AgArch;
import jason.asSemantics.ActionExec;
import jason.asSemantics.Agent;
import jason.asSemantics.Circumstance;
import jason.asSemantics.Intention;
import jason.asSemantics.Message;
import jason.asSemantics.TransitionSystem;
import jason.asSemantics.Tuple;
import jason.asSyntax.Atom;
import jason.asSyntax.Literal;
import jason.asSyntax.LiteralImpl;
import jason.asSyntax.Plan;
import jason.asSyntax.PlanBody;
import jason.asSyntax.Trigger;
import jason.asSyntax.Trigger.TEOperator;
import jason.asSyntax.Trigger.TEType;
import jason.mas2j.ClassParameters;
import jason.runtime.RuntimeServices;
import jason.runtime.RuntimeServicesFactory;
import jason.runtime.Settings;
import jason.util.Config;

/**
 * This class provides an agent architecture when using Local
 * infrastructure to run the MAS inside Jason.
 *
 * Each agent has its own thread.
 *
 * <p>
 * Execution sequence:
 * <ul>
 * <li>initAg,
 * <li>setEnvInfraTier,
 * <li>setControlInfraTier,
 * <li>run (perceive, checkMail, act),
 * <li>stopAg.
 * </ul>
 */
public class LocalAgArch extends AgArch implements Runnable, Serializable {

    private static final long serialVersionUID = 4378889704809002271L;

    protected transient LocalEnvironment      infraEnv     = null;
    private   transient LocalExecutionControl infraControl = null;
    private   transient BaseLocalMAS          masRunner    = BaseLocalMAS.getRunner();

    private String             agName  = "";
    private volatile boolean   running = true;
    private Queue<Message>     mbox    = new ConcurrentLinkedQueue<>();
    protected transient Logger logger  = Logger.getLogger(LocalAgArch.class.getName());

    private static List<MsgListener> msgListeners = null;

    /** Mapping of cpX → functor name */
    private final Map<Integer, String> cpBindings = new LinkedHashMap<>();

    /** Last seen severity label for each cp */
    private final Map<Integer, String> lastVals = new HashMap<>();

    // RosMaster added for instant trigger of Critical Severity perceptions
    //private MyRosMaster myRosMaster;

    private static final Map<String, Integer> cpToPriority = new HashMap<>();
    static {
        Map.of(
            5, List.of("cp4"),             //Catastrophic
            4, List.of("cp1" ),                   //Hazardous
            3, List.of("cp0"),                  //Major
            2, List.of("cp2"),            //Minor
            1, List.of("cp3")             //No Effect
        ).forEach((prio, cps) -> cps.forEach(cp -> cpToPriority.put(cp, prio)));
    }

    private static final Map<Integer, String> priorityToMode = new HashMap<>();
    static {
        priorityToMode.put(5, "Bypass");
        priorityToMode.put(4, "Expedited-RC");
        priorityToMode.put(3, "Expedited-RC");
        priorityToMode.put(2, "Standard-RC");
        priorityToMode.put(1, "Standard-RC");
    }

    /** Mapping of cp functor -> reaction string (e.g., "cp1" -> "react_cp1") */
    private static final Map<String, String> cpReactions = new HashMap<>();
    static {
        cpReactions.put("cp0", "cp0_Minor");    // !react_cp0
        cpReactions.put("cp1", "cp1_Major");    // react_cp1 [cr]
        cpReactions.put("cp2", "cp2_Catastrophic");  //  internalAction(cp2-Catastrophic)
        cpReactions.put("cp3", "react_cp3");    
        cpReactions.put("cp4", "failsafe_2");
        cpReactions.put("cp5", "react_cp5");
        cpReactions.put("cp6", "react_cp6");
        cpReactions.put("cp7", "failsafe_2");
        cpReactions.put("cp8", "react_cp8");
        cpReactions.put("cp9", "cp9_catastrophic");
    }

    public static void addMsgListener(MsgListener l) {
        if (msgListeners == null) {
            msgListeners = new ArrayList<>();
        }
        msgListeners.add(l);
    }
    public static void removeMsgListener(MsgListener l) {
        msgListeners.remove(l);
    }

    private void readObject(ObjectInputStream inputStream) throws IOException, ClassNotFoundException {
        inputStream.defaultReadObject();
        sleepSync   = new Object();
        syncMonitor = new Object();
        masRunner   = BaseLocalMAS.getRunner();
    }

    public LocalAgArch() {
        super();

        // Bind cp0 directly to "cp0"
        cpToPriority.entrySet().stream()
        .sorted((a, b) -> Integer.compare(b.getValue(), a.getValue())) // Descending priority
        .forEach(entry -> {
            String cp = entry.getKey(); // e.g., "cp7"
            try {
                int cpIndex = Integer.parseInt(cp.replace("cp", ""));
                cpBindings.put(cpIndex, cp);
                lastVals.put(cpIndex, "None");
            } catch (NumberFormatException e) {
                System.err.println("Invalid CP key format: " + cp);
            }
        });

        }
    /**
     * Creates the user agent architecture, default architecture is
     * jason.architecture.AgArch. The arch will create the agent that creates
     * the TS.
     */
    public void createArchs(Collection<String> agArchClasses, String agClass, ClassParameters bbPars, String asSrc, Settings stts) throws Exception {
        try {
            Agent.create(this, agClass, bbPars, asSrc, stts);
            insertAgArch(this);

            createCustomArchs(agArchClasses);

            // mind inspector arch
            if (stts.getUserParameter(Settings.MIND_INSPECTOR) != null) {
                insertAgArch( (AgArch)Class.forName( Config.get().getMindInspectorArchClassName()).getConstructor().newInstance() );
                getFirstAgArch().init();
            }

            setLogger();
        } catch (Exception e) {
            running = false;
            throw e; //new JasonException("as2j: error creating the agent class! - "+e.getMessage(), e);
        }
    }

    /** init the agent architecture based on another agent */
    public void createArchs(Collection<String> agArchClasses, Agent ag) throws JasonException {
        try {
            setMASRunner(masRunner); // TODO: remove
            setTS(ag.clone(this).getTS());
            insertAgArch(this);

            createCustomArchs(agArchClasses);

            setLogger();
        } catch (Exception e) {
            running = false;
            throw new JasonException("as2j: error creating the agent class! - ", e);
        }
    }

    public void setMASRunner(BaseLocalMAS masRunner) {
        this.masRunner = masRunner;
    }


    public void stopAg() {
        running = false;
        wake(); // so that it leaves the run loop
        if (myThread != null)
            myThread.interrupt();
        getTS().getAg().stopAg();

        // stop all archs
        AgArch f = getUserAgArch();
        while (f != null) {
            f.stop();
            f = f.getNextAgArch();
        }
    }


    public void setLogger() {
        logger = Logger.getLogger(LocalAgArch.class.getName() + "." + getAgName());
        if (getTS().getSettings().verbose() >= 0)
            logger.setLevel(getTS().getSettings().logLevel());
    }

    public Logger getLogger() {
        return logger;
    }

    public void setAgName(String name) throws JasonException {
        if (name.equals("self"))
            throw new JasonException("an agent cannot be named 'self'!");
        if (name.equals("percept"))
            throw new JasonException("an agent cannot be named 'percept'!");
        agName = name;
    }

    public String getAgName() {
        return agName;
    }

    /**
     *
     * @deprecated use getFirstAgArch instead
     */
    @Deprecated
    public AgArch getUserAgArch() {
        return getFirstAgArch();
    }

    public void setEnvInfraTier(LocalEnvironment env) {
        infraEnv = env;
    }

    public LocalEnvironment getEnvInfraTier() {
        return infraEnv;
    }

    public void setControlInfraTier(LocalExecutionControl pControl) {
        infraControl = pControl;
    }

    public LocalExecutionControl getControlInfraTier() {
        return infraControl;
    }

    private transient Thread myThread = null;
    public void setThread(Thread t) {
        myThread = t;
        myThread.setName(agName);
    }
    public Thread getThread() {
        return myThread;
    }
    public void startThread() {
        if (!myThread.isAlive())
            myThread.start();
    }

    public boolean isRunning() {
        return running;
    }

    protected void sense() {
        TransitionSystem ts = getTS();

        int i = 0;
        do {
            ts.sense(); // must run at least once, so that perceive() is called
        } while (running && ++i < cyclesSense && !ts.canSleepSense());
    }

    protected void expeditedRP() {
        TransitionSystem ts = getTS();

        int i = 0;
        do { 
            ts.expeditedRP();
        } while (running && ++i < cyclesSense && !ts.canSleepSense());
    }

    //int sumDel = 0; int nbDel = 0;
    protected void deliberate() {
        TransitionSystem ts = getTS();
        int i = 0;
        while (running && i++ < cyclesDeliberate && !ts.canSleepDeliberate()) {
            ts.deliberate();
        }
        //sumDel += i; nbDel++;
        //System.out.println("running del "+(sumDel/nbDel)+"/"+cyclesDeliberate);
    }

    /** the act as step of reasoning cycle */
    //int sumAct = 0; int nbAct = 0;
    protected void act() {
        TransitionSystem ts = getTS();

        int i = 0;
        int ca = cyclesAct;
        if (ca != 1) { // not the default value, limit the value to the number of intentions
            ca = Math.min(cyclesAct, ts.getC().getNbRunningIntentions());
            if (ca == 0)
                ca = 1;
        }
        while (running && i++ < ca && !ts.canSleepAct()) {
            ts.act();
        }
        //sumAct += i; nbAct++;
        //System.out.println("running act "+(sumAct/nbAct)+"/"+ca);
    }

    protected void reasoningCycle() {
    //     getFirstAgArch().reasoningCycleStarting();

    //     sense();
    //     deliberate();
    //     act();

    //     getFirstAgArch().reasoningCycleFinished();

    //LBB attempt 1:
    //long start = System.currentTimeMillis();

        getFirstAgArch().reasoningCycleStarting();
        long start = System.nanoTime();

        //criticalRC();
        // TransitionSystem ts = getTS(); 
        // ts.expeditedRP();
        getTS().expeditedRP();
        long endSenLBB = System.nanoTime();
        sense();
        long endSen = System.nanoTime();
        deliberate();
        long endDel = System.nanoTime();
        act();
        long endRC = System.nanoTime();

        getFirstAgArch().reasoningCycleFinished();
        //long pass = System.currentTimeMillis() - start;
  
    }

    public void run() {
        TransitionSystem ts = getTS();
        /*cpToPriority.entrySet().stream()
        .sorted((a, b) -> Integer.compare(b.getValue(), a.getValue())) // Descending priority
        .forEach(entry -> {
            String cp = entry.getKey(); // e.g., "cp7"
            try {
                int cpIndex = Integer.parseInt(cp.replace("cp", ""));
                cpBindings.put(cpIndex, cp);
                lastVals.put(cpIndex, "None");
            } catch (NumberFormatException e) {
                System.err.println("Invalid CP key format: " + cp);
            }
        });*/
        /*try {
            // Pause for 1 second (1000 milliseconds)
            Thread.sleep(10); 
        } catch (InterruptedException e) {
            // It is best practice to restore the interrupt flag
            Thread.currentThread().interrupt(); 
            System.out.println("Thread was interrupted!");
        }*/
        while (running) {
            if (ts.getSettings().isSync()) {
                waitSyncSignal();
                reasoningCycle();
                boolean isBreakPoint = false;
                try {
                    isBreakPoint = ts.getC().getSelectedOption().getPlan().hasBreakpoint();
                    if (logger.isLoggable(Level.FINE)) logger.fine("Informing controller that I finished a reasoning cycle "+getCycleNumber()+". Breakpoint is " + isBreakPoint);
                } catch (NullPointerException e) {
                    // no problem, there is no sel opt, no plan ....
                }
                informCycleFinished(isBreakPoint, getCycleNumber());
            } else {
                getFirstAgArch().incCycleNumber(); // should not increment in case of sync execution
                reasoningCycle();
                if (ts.canSleep())
                    sleepCJ(); 
            }
        }
        logger.fine("I finished!");
    }

    private transient Object sleepSync = new Object();
    private int    sleepTime = 50;

    public static final int MAX_SLEEP = 1000;

    public void sleep() {
        try {
            if (!getTS().getSettings().isSync()) {
                //logger.fine("Entering in sleep mode....");
                synchronized (sleepSync) {
                    sleepSync.wait(sleepTime); // wait for messages
                    if (sleepTime < MAX_SLEEP)
                        sleepTime += 100;
                }
            }
        } catch (InterruptedException e) {
        } catch (Exception e) {
            logger.log(Level.WARNING,"Error in sleep.", e);
        }
    }

    // LBB: modified to a fixed 100ms sleep
    public void sleepCJ() {
        int i=10;
        try {
            if (!getTS().getSettings().isSync()) {
                while(i-- > 0){
                    //logger.info("Entering in sleep mode....");
                    synchronized (sleepSync) {
                        sleepSync.wait(10); // wait for messages
                    }
                    if(perceiveCP() != null){
                        break;
                    }                         
                }
            }
        } catch (InterruptedException e) {
        } catch (Exception e) {
            logger.log(Level.WARNING,"Error in sleep.", e);
        }
    }

    @Override
    public void wake() {
        synchronized (sleepSync) {
            sleepTime = 50;
            sleepSync.notifyAll(); // notify sleep method
        }
    }

    @Override
    public void wakeUpSense() {
        wake();
    }

    @Override
    public void wakeUpDeliberate() {
        wake();
    }

    @Override
    public void wakeUpAct() {
        wake();
    }

    // Default perception assumes Complete and Accurate sensing.
    @Override
    public Collection<Literal> perceive() {
        super.perceive();
        if (infraEnv == null) return null;
        Collection<Literal> percepts = infraEnv.getUserEnvironment().getPercepts(getAgName());
        //if (logger.isLoggable(Level.FINE) && percepts != null) logger.fine("percepts: " + percepts);
        return percepts;
    }

    /* LBB implementartion for critical things
     * If 'infraEnv' is NULL it means this function will not be used, and another implementation is provided in a different xxAgArch implementation (eg. DemoEmbeddedAgentArch)
     */
   @Override
    public Boolean[] perceiveCP() { 
        super.perceiveCP();
        if (infraEnv == null) return null;
        Boolean[] EnvPercepts = infraEnv.getUserEnvironment().getPerceptsCBS(getAgName());
        Circumstance C = getTS().getC();
        C.CPM.clear();
        for (Map.Entry<Integer, String> binding : cpBindings.entrySet()) {
            String functor = binding.getValue(); // e.g., "cp0"
            int cpIndex = Integer.parseInt(functor.replace("cp", ""));
            if (EnvPercepts[cpIndex] == Boolean.FALSE) continue;
            int priority = getPriority(functor);
            String reaction = cpReactions.getOrDefault(functor, "handle_" + functor);
            String mode = priorityToMode.get(priority);
            int k = 0;
            try {
                switch (mode) {
                    case "Bypass":
                        ActionExec action = null;
                        action = new ActionExec(new LiteralImpl("critReac0"), null); //LBB: FIX for proper function, e.g. ag.selectActionLB()
                        act(action);
                        infraEnv.getUserEnvironment().resetCBS();
                        break;

                    case "Expedited-RC":
                        Literal percept = new LiteralImpl("cb"+cpIndex); 
                        Trigger te = new Trigger(TEOperator.add, TEType.belief, percept);
                        C.CPM.put(te.getPredicateIndicator(), true);
                        break;

                    default: // Standard-RC
                        Literal lit = Literal.parseLiteral("cr0Per(" + k + ")");
                        infraEnv.getUserEnvironment().addPercept(lit);
                        k=k+1;
                }
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
        return EnvPercepts;
    }

    private int getPriority(String functor) {
        return cpToPriority.getOrDefault(functor, 3);
    }

    // this is used by the .send internal action in stdlib
    public void sendMsg(Message m) throws ReceiverNotFoundException {
        // actually send the message
        if (m.getSender() == null)  m.setSender(getAgName());

        LocalAgArch rec = masRunner.getAg(m.getReceiver());

        if (rec == null) {
            if (isRunning())
                throw new ReceiverNotFoundException("Receiver '" + m.getReceiver() + "' does not exist! Could not send " + m, m.getReceiver());
            else
                return;
        }
        rec.receiveMsg(m.clone()); // send a cloned message

        // notify listeners
        if (msgListeners != null)
            for (MsgListener l: msgListeners)
                l.msgSent(m);
    }

    public void receiveMsg(Message m) {
        mbox.offer(m);
        wakeUpSense();
    }

    public void broadcast(Message m) throws Exception {
        for (String agName: RuntimeServicesFactory.get().getAgentsNames()) {
            if (!agName.equals(this.getAgName())) {
                Message newm = m.clone();
                newm.setReceiver(agName);
                getFirstAgArch().sendMsg(newm);
            }
        }
    }

    // Default procedure for checking messages, move message from local mbox to C.mbox
    public void checkMail() {
        Circumstance C = getTS().getC();
        Message im = mbox.poll();
        while (im != null) {
            C.addMsg(im);
            if (logger.isLoggable(Level.FINE)) logger.fine("received message: " + im);
            im = mbox.poll();
        }
    }

    public Collection<Message> getMBox() {
        return mbox;
    }

    /** called by the TS to ask the execution of an action in the environment */
    @Override
    public void act(ActionExec action) {
        //if (logger.isLoggable(Level.FINE)) logger.fine("doing: " + action.getActionTerm());

        if (isRunning()) {
            if (infraEnv != null) {
                infraEnv.act(getAgName(), action);
            } else {
                action.setResult(false);
                action.setFailureReason(new Atom("noenv"), "no environment configured!");
                actionExecuted(action);
            }
        }
    }

    public boolean canSleep() {
        return mbox.isEmpty() && isRunning();
    }

    private transient Object  syncMonitor = new Object();
    private volatile boolean inWaitSyncMonitor = false;

    /**
     * waits for a signal to continue the execution (used in synchronised
     * execution mode)
     */
    private void waitSyncSignal() {
        try {
            synchronized (syncMonitor) {
                inWaitSyncMonitor = true;
                syncMonitor.wait();
                inWaitSyncMonitor = false;
            }
        } catch (InterruptedException e) {
        } catch (Exception e) {
            logger.log(Level.WARNING,"Error waiting sync (1)", e);
        }
    }

    /**
     * inform this agent that it can continue, if it is in sync mode and
     * waiting a signal
     */
    public void receiveSyncSignal() {
        try {
            synchronized (syncMonitor) {
                while (!inWaitSyncMonitor && isRunning()) {
                    // waits the agent to enter in waitSyncSignal
                    syncMonitor.wait(50);
                }
                syncMonitor.notifyAll();
            }
        } catch (InterruptedException e) {
        } catch (Exception e) {
            logger.log(Level.WARNING,"Error waiting sync (2)", e);
        }
    }

    /**
     *  Informs the infrastructure tier controller that the agent
     *  has finished its reasoning cycle (used in sync mode).
     *
     *  <p><i>breakpoint</i> is true in case the agent selected one plan
     *  with the "breakpoint" annotation.
     */
    public void informCycleFinished(boolean breakpoint, int cycle) {
        infraControl.receiveFinishedCycle(getAgName(), breakpoint, cycle);
    }

    public RuntimeServices getRuntimeServices() {
        return RuntimeServicesFactory.get();
    }

    private RConf conf;

    private int cycles = 1;

    private int cyclesSense      = 1;
    private int cyclesDeliberate = 1;
    private int cyclesAct        = 1;

    public void setConf(RConf conf) {
        this.conf = conf;
    }

    public RConf getConf() {
        return conf;
    }

    public int getCycles() {
        return cycles;
    }

    public void setCycles(int cycles) {
        this.cycles = cycles;
    }

    public int getCyclesSense() {
        return cyclesSense;
    }

    public void setCyclesSense(int cyclesSense) {
        this.cyclesSense = cyclesSense;
    }

    public int getCyclesDeliberate() {
        return cyclesDeliberate;
    }

    public void setCyclesDeliberate(int cyclesDeliberate) {
        this.cyclesDeliberate = cyclesDeliberate;
    }

    public int getCyclesAct() {
        return cyclesAct;
    }

    public void setCyclesAct(int cyclesAct) {
        this.cyclesAct = cyclesAct;
    }

    @Override
    public Map<String, Object> getStatus() {
        Map<String, Object> status = super.getStatus();

        status.put("cycle", getCycleNumber());
        status.put("idle", getTS().canSleep());

        // put intentions
        Circumstance c = getTS().getC();

        status.put("nbIntentions", c.getNbRunningIntentions() + c.getPendingIntentions().size());

        List<Map<String, Object>> ints = new ArrayList<>();
        Iterator<Intention> ii = c.getAllIntentions();
        while (ii.hasNext()) {
            Intention i = ii.next();
            Map<String, Object> iprops = new HashMap<>();
            iprops.put("id", i.getId());
            iprops.put("finished", i.isFinished());
            //iprops.put("suspended", i.isSuspended());
            iprops.put("state", i.getStateBasedOnPlace());
            if (i.isSuspended()) {
                iprops.put("suspendedReason", i.getSuspendedReason().toString());
            }
            iprops.put("size", i.size());
            ints.add(iprops);
        }
        status.put("intentions", ints);

        return status;
    }
}
