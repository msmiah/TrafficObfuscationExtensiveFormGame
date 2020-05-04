package extensive_form_game_solver;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;

import extensive_form_game.Game;
import extensive_form_game.Game.Action;
import extensive_form_game.Game.Node;
import gnu.trove.iterator.TIntDoubleIterator;
import gnu.trove.iterator.TIntObjectIterator;
import gnu.trove.list.TIntList;
import gnu.trove.list.array.TIntArrayList;
import gnu.trove.map.TIntDoubleMap;
import gnu.trove.map.TIntObjectMap;
import gnu.trove.map.TObjectDoubleMap;
import gnu.trove.map.TObjectIntMap;
import gnu.trove.map.hash.TIntDoubleHashMap;
import gnu.trove.map.hash.TIntObjectHashMap;
import gnu.trove.map.hash.TObjectDoubleHashMap;
import gnu.trove.map.hash.TObjectIntHashMap;
import gnu.trove.set.TIntSet;
import gnu.trove.set.hash.TIntHashSet;
import ilog.cplex.*;
import ilog.concert.*;
import ilog.cplex.IloCplex;
import ilog.cplex.IloCplex.UnknownObjectException;
import utils.Utils;

public class StackleBergNaiveSolver<E> extends ZeroSumGameSolver {
	Game game;

	int playerToSolveFor;
	int playerNotToSolveFor;

	IloCplex cplex;
	IloLinearNumExpr objective;
	IloLinearNumExpr natureConstraints;
	// IloNumVar[] modelStrategyVars;
	IloNumVar[] dualVars; // indexed as [informationSetId]. Note that we expect information sets to be
							// 1-indexed, but the code corrects for when this is not the case
	HashMap<String, IloNumVar>[] strategyVarsByInformationSet; // indexed as [inforationSetId][action.name]
	HashMap<String, String>[] opponentStrategyVarsByInformationSet; // indexed as [inforationSetId][action.name]
	HashMap<String, Boolean> opponentBrStrategy;
	TIntList[] sequenceFormDualMatrix; // indexed as [dual sequence id][information set]
	TIntDoubleMap[] sequenceFormDualProbMatrix;
	TIntDoubleMap[] sequenceFormDualP1Matrix;
	TIntDoubleMap[] dualPayoffMatrix; // indexed as [dual sequence][primal sequence]
	TIntDoubleMap[] p1PayoffMatrix;
	TIntDoubleMap[] symmetricActionCntInP2InformationSet;
	TIntObjectMap<String>[] modelStrategyVars;
	TObjectIntMap<String>[] sequenceIdByInformationSetAndActionChance;
	TObjectIntMap<String>[] sequenceIdByInformationSetAndActionP1; // indexed as [informationSetId][action.name]
	TObjectIntMap<String>[] sequenceIdByInformationSetAndActionP2; // indexed as [informationSetId][action.name]
	IloNumVar[] strategyVarsBySequenceId;
	String[] opponentStrategyVarsBySequenceId;
	IloNumVar[] zVarsBySequenceId;

	int[] p2InformationSetBySequenceId;
	int numSequencesP1;
	int numSequencesP2;
	int numPrimalSequences;
	int numDualSequences;
	int numPrimalInformationSets;
	int numDualInformationSets;
	int numSequencesNature;

	String[] dualSequenceNames;
	String[] primalSequenceNames;

	TIntObjectMap<IloConstraint> primalConstraints; // indexed as [informationSetId], without correcting for 1-indexing
	TIntObjectMap<IloRange> dualConstraints; // indexed as [sequenceId]
	double[] nodeNatureProbabilities; // indexed as [nodeId]. Returns the probability of that node being reached when
										// considering only nature nodes
	int[] sequenceIdForNodeP1; // indexed as [nodeId]. Returns the sequenceId of the last sequence belonging to
								// Player 1 on the path to the node.
	int[] sequenceIdForNodeP2; // indexed as [nodeId]. Returns the sequenceId of the last sequence belonging to
								// Player 2 on the path to the node.
	int cnt = 0;
	double[] tempModificationCost = { 1.0, 1.0, 2.0, 2.0, };

	public StackleBergNaiveSolver(Game game, int playerToSolveFor) {
		this(game, playerToSolveFor, 1e-6);
	}

	public StackleBergNaiveSolver(Game game, int playerToSolveFor, double tol) {
		super(game);
		this.game = game;
		try {
			cplex = new IloCplex();
		} catch (IloException e) {
			System.out.println("Error SequenceFormLPSolver(): CPLEX setup failed");
		}

		this.playerToSolveFor = playerToSolveFor;
		this.playerNotToSolveFor = (playerToSolveFor % 2) + 1;

		initializeDataStructures();

		try {
			setUpModel(tol);
		} catch (IloException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Initializes the arrays and other data structure objects that we use.
	 */
	@SuppressWarnings("unchecked")
	private void initializeDataStructures() {
		int numInformationSets = 0;
		int opponentNumInformationSets = 0;

		if (playerToSolveFor == 1) {
			numInformationSets = game.getNumInformationSetsPlayer1();
			opponentNumInformationSets = game.getNumInformationSetsPlayer2();
		} else {
			numInformationSets = game.getNumInformationSetsPlayer2();
			opponentNumInformationSets = game.getNumInformationSetsPlayer1();
		}
		this.strategyVarsByInformationSet = (HashMap<String, IloNumVar>[]) new HashMap[numInformationSets + 1];
		this.opponentStrategyVarsByInformationSet = (HashMap<String, String>[]) new HashMap[opponentNumInformationSets
				+ 1];
		this.opponentBrStrategy = new HashMap<String, Boolean>();
		for (int i = 0; i <= numInformationSets; i++) {
			this.strategyVarsByInformationSet[i] = new HashMap<String, IloNumVar>();
		}

		for (int i = 0; i <= opponentNumInformationSets; i++) {
			this.opponentStrategyVarsByInformationSet[i] = new HashMap<String, String>();

		}
		numPrimalSequences = playerToSolveFor == 1 ? game.getNumSequencesP1() : game.getNumSequencesP2();
		numDualSequences = playerNotToSolveFor == 1 ? game.getNumSequencesP1() : game.getNumSequencesP2();

		sequenceFormDualMatrix = new TIntList[numDualSequences];
		sequenceFormDualProbMatrix = new TIntDoubleHashMap[numDualSequences];
		sequenceFormDualP1Matrix = new TIntDoubleHashMap[numDualSequences];
		for (int i = 0; i < numDualSequences; i++) {
			sequenceFormDualMatrix[i] = new TIntArrayList();
			sequenceFormDualProbMatrix[i] = new TIntDoubleHashMap();
			sequenceFormDualP1Matrix[i] = new TIntDoubleHashMap();
		}

		numPrimalInformationSets = playerToSolveFor == 1 ? game.getNumInformationSetsPlayer1()
				: game.getNumInformationSetsPlayer2();
		numDualInformationSets = playerNotToSolveFor == 1 ? game.getNumInformationSetsPlayer1()
				: game.getNumInformationSetsPlayer2();

		dualSequenceNames = new String[numDualSequences];
		primalSequenceNames = new String[numDualSequences];

		dualPayoffMatrix = new TIntDoubleHashMap[numDualSequences];
		symmetricActionCntInP2InformationSet = new TIntDoubleHashMap[numDualSequences];
		modelStrategyVars = new TIntObjectHashMap[numDualSequences];
		p1PayoffMatrix = new TIntDoubleHashMap[numDualSequences];

		for (int i = 0; i < numDualSequences; i++) {
			dualPayoffMatrix[i] = new TIntDoubleHashMap();
			symmetricActionCntInP2InformationSet[i] = new TIntDoubleHashMap();
			p1PayoffMatrix[i] = new TIntDoubleHashMap();
			modelStrategyVars[i] = new TIntObjectHashMap<>();
		}
		// ensure that we have a large enough array for both the case where information
		// sets start at 1 and 0
		sequenceIdByInformationSetAndActionChance = new TObjectIntMap[1 + 1];
		sequenceIdByInformationSetAndActionP1 = new TObjectIntMap[game.getNumInformationSetsPlayer1() + 1];
		sequenceIdByInformationSetAndActionP2 = new TObjectIntMap[game.getNumInformationSetsPlayer2() + 1];
		for (int i = 0; i < 2; i++) {
			sequenceIdByInformationSetAndActionChance[i] = new TObjectIntHashMap<String>();
		}
		for (int i = 0; i <= game.getNumInformationSetsPlayer1(); i++) {
			sequenceIdByInformationSetAndActionP1[i] = new TObjectIntHashMap<String>();
		}
		for (int i = 0; i <= game.getNumInformationSetsPlayer2(); i++) {
			sequenceIdByInformationSetAndActionP2[i] = new TObjectIntHashMap<String>();
		}

		if (playerToSolveFor == 1) {
			strategyVarsBySequenceId = new IloNumVar[game.getNumSequencesP1()];
			opponentStrategyVarsBySequenceId = new String[game.getNumSequencesP2()];
			zVarsBySequenceId = new IloNumVar[game.getNumSequencesP1()];
			p2InformationSetBySequenceId = new int[game.getNumSequencesP1()];
		} else {
			strategyVarsBySequenceId = new IloNumVar[game.getNumSequencesP2()];
			p2InformationSetBySequenceId = new int[game.getNumSequencesP2()];
		}

		primalConstraints = new TIntObjectHashMap<IloConstraint>();
		dualConstraints = new TIntObjectHashMap<IloRange>();
		nodeNatureProbabilities = new double[game.getNumNodes() + 1]; // Use +1 to be robust for non-zero indexed nodes
		sequenceIdForNodeP1 = new int[game.getNumNodes() + 1];
		sequenceIdForNodeP2 = new int[game.getNumNodes() + 1];

	}

	/**
	 * Tries to solve the current model. Currently relies on CPLEX to throw an
	 * exception if no model has been built.
	 */
	@Override
	public void solveGame() {
		try {
			System.out.println(" Length " + strategyVarsBySequenceId.length);

			if (cplex.solve()) {
				for (int i = 0; i < strategyVarsBySequenceId.length; i++) {
					// System.out.println("Sequence = " + strategyVarsBySequenceId[i]);
					IloNumVar v = strategyVarsBySequenceId[i];
					// if(v != null)
					// System.out.println("Cplex val : " + cplex.getValue(v));
				}
				valueOfGame = cplex.getObjValue();
				System.out.println("Defender's utility in StackleBerg Game : " + valueOfGame);
			}

		} catch (IloException e) {
			e.printStackTrace();
			System.out.println("Error SequenceFormLPSolver::solveGame: solve exception");
		}
	}
	
	public double getGameValue() {
		return valueOfGame;
	}
	/**
	 * Creates and returns a mapping from variable names to the values they take on
	 * in the solution computed by CPLEX.
	 */
	public TObjectDoubleMap<String> getStrategyVarMap() {
		TObjectDoubleMap<String> map = new TObjectDoubleHashMap<String>();
		for (IloNumVar v : strategyVarsBySequenceId) {
			try {
				map.put(v.getName(), cplex.getValue(v));
			} catch (UnknownObjectException e) {
				e.printStackTrace();
			} catch (IloException e) {
				e.printStackTrace();
			}
		}

		return map;
	}

	/**
	 * Creates and returns a mapping from information set id and action name pairs
	 * to the probability of taking that action in the computed solutionc
	 */
	@SuppressWarnings("unchecked")
	public TObjectDoubleMap<String>[] getInformationSetActionProbabilities() {
		TObjectDoubleMap<String>[] map = new TObjectDoubleHashMap[numPrimalInformationSets];
		for (int informationSetId = 0; informationSetId < numPrimalInformationSets; informationSetId++) {
			map[informationSetId] = new TObjectDoubleHashMap();
			double sum = 0;
			for (String actionName : strategyVarsByInformationSet[informationSetId].keySet()) {
				try {
					sum += cplex.getValue(strategyVarsByInformationSet[informationSetId].get(actionName));
				} catch (IloException e) {
					e.printStackTrace();
				}
			}
			for (String actionName : strategyVarsByInformationSet[informationSetId].keySet()) {
				try {
					if (sum > 0) {
						map[informationSetId].put(actionName,
								cplex.getValue(strategyVarsByInformationSet[informationSetId].get(actionName)) / sum);
					} else {
						map[informationSetId].put(actionName, 0);
					}
				} catch (IloException e) {
					e.printStackTrace();
				}
			}
		}
		return map;
	}

	/**
	 * Creates and returns a mapping from information set id and action name pairs
	 * to the probability of taking that action in the computed solution
	 */
	public TIntDoubleMap[] getInformationSetActionProbabilitiesByActionId() {
		TIntDoubleMap[] map = new TIntDoubleHashMap[numPrimalInformationSets];
		for (int informationSetId = 0; informationSetId < numPrimalInformationSets; informationSetId++) {
			map[informationSetId] = new TIntDoubleHashMap();
			double sum = 0;
			for (String actionName : strategyVarsByInformationSet[informationSetId].keySet()) {
				try {
					sum += cplex.getValue(strategyVarsByInformationSet[informationSetId].get(actionName));
				} catch (IloException e) {
					e.printStackTrace();
				}
			}
			for (int actionId = 0; actionId < game.getNumActionsAtInformationSet(playerToSolveFor,
					informationSetId); actionId++) {
				String actionName = game.getActionsAtInformationSet(playerToSolveFor, informationSetId)[actionId]
						.getName();
				try {
					if (sum > 0) {
						map[informationSetId].put(actionId,
								cplex.getValue(strategyVarsByInformationSet[informationSetId].get(actionName)) / sum);
					} else {
						map[informationSetId].put(actionId, 0);
					}
				} catch (IloException e) {
					e.printStackTrace();
				}
			}
		}
		return map;
	}

	/**
	 * Prints the value of the game along with the names and computed values for
	 * each variable.
	 */
	@Override
	public void printStrategyVarsAndGameValue() {
		printGameValue();
		for (IloNumVar v : strategyVarsBySequenceId) {
			try {
				if (null != v)
					System.out.println(v.getName() + ": \t" + cplex.getValue(v));
			} catch (UnknownObjectException e) {
				e.printStackTrace();
			} catch (IloException e) {
				e.printStackTrace();
			}
		}
	}

	/**
	 * Prints the value of the game, as computed by CPLEX. If solve() has not been
	 * called, an exception will be thrown.
	 */
	@Override
	public void printGameValue() {
		try {
			System.out.println("Solve status: " + cplex.getStatus());
			if (cplex.getStatus() == IloCplex.Status.Optimal) {
				System.out.println("Objective value: " + this.valueOfGame);
			}
		} catch (IloException e) {
			e.printStackTrace();
		}

	}

	/**
	 * Writes the computed strategy to a file. An exception is thrown if solve() has
	 * not been called.
	 * 
	 * @param filename
	 *            the absolute path to the file being written to
	 */
	public void writeStrategyToFile(String filename) throws IloException {
		try {
			FileWriter fw = new FileWriter(filename);
			fw.write("...............Defender's strategy................\n");
			for (IloNumVar v : strategyVarsBySequenceId) {
				if (v != null)
					//cplex.add(v);
					//System.out.println(v);

					if (cplex.getValue(v) < 0.00005)
						fw.write(v.getName() + ": \t" + 0.0 + "\n");
					else
						fw.write(v.getName() + ": \t" + cplex.getValue(v) + "\n");
			}		
			fw.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Writes the current model to a file. CPLEX throws an exception if the model is
	 * faulty or the path does not exist.
	 * 
	 * @param filename
	 *            the absolute path to the file being written to
	 */
	public void writeModelToFile(String filename) {
		try {
			cplex.exportModel(filename);
		} catch (IloException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Sets the parameters of CPLEX such that minimal output is produced.
	 */
	private void setCplexParameters(double tol) {
		try {
			cplex.setParam(IloCplex.IntParam.RootAlg, IloCplex.Algorithm.Barrier);
			cplex.setParam(IloCplex.DoubleParam.EpOpt, tol);
			cplex.setParam(IloCplex.DoubleParam.BarEpComp, tol);
			cplex.setParam(IloCplex.IntParam.BarCrossAlg, -1);
			// cplex.setParam(IloCplex.IntParam.SimDisplay, 0);
			// cplex.setParam(IloCplex.IntParam.MIPDisplay, 0);
			// cplex.setParam(IloCplex.IntParam.MIPInterval, -1);
			// cplex.setParam(IloCplex.IntParam.TuningDisplay, 0);
			// cplex.setParam(IloCplex.IntParam.BarDisplay, 0);
			// cplex.setParam(IloCplex.IntParam.SiftDisplay, 0);
			// cplex.setParam(IloCplex.IntParam.ConflictDisplay, 0);
			// cplex.setParam(IloCplex.IntParam.NetDisplay, 0);
			cplex.setParam(IloCplex.DoubleParam.TiLim, 1e+75);
		} catch (IloException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Builds the LP model based on the game instance.
	 * 
	 * @throws IloException
	 */
	private void setUpModel(double tol) throws IloException {
		setCplexParameters(tol);

		objective = cplex.linearNumExpr();
		natureConstraints = cplex.linearNumExpr();
		// The empty sequence is the 0'th sequence for each player
		numSequencesNature = numSequencesP1 = numSequencesP2 = 1;
		primalSequenceNames[0] = "root";
		dualSequenceNames[0] = "root";
		CreateSequenceFormIds(game.getRoot(), new TIntHashSet(), new TIntHashSet());
		assert (numSequencesP1 == game.getNumSequencesP1()); // Ensure that our recursive function agrees with the game
																// reader on how many sequences there are
		assert (numSequencesP2 == game.getNumSequencesP2());

		// create root sequence var
		IloNumVar rootSequence = cplex.numVar(1, 1, "I_root");
		strategyVarsBySequenceId[0] = rootSequence;

		System.out.println("************************ Equation no 4  ************************************");
		CreateSequenceFormVariablesAndConstraints(game.getRoot(),0,0, rootSequence, null, new TIntHashSet(), new TIntHashSet(),
				1,1);

		CreateDualVariablesAndConstraints();
		// System.out.println(natureConstraints);
		// cplex.addEq(natureConstraints, rootSequence);
		SetObjective();
	}

	/**
	 * Recursive function that traverses the game tree, assigning Id values,
	 * starting at 1 due to the empty sequence, to sequences in pre-order. Sequence
	 * IDs are only assigned if an information set has not previously been visited
	 * 
	 * @param currentNodeId
	 *            id into the game.nodes array
	 * @param visitedP1
	 *            an integer set indicating which information sets have already been
	 *            visited for Player 1
	 * @param visitedP2
	 *            an integer set indicating which information sets have already been
	 *            visited for Player 2
	 */
	private void CreateSequenceFormIds(int currentNodeId, TIntSet visitedP1, TIntSet visitedP2) {
		Node node = game.getNodeById(currentNodeId);
		if (node.isLeaf())
			return;

		for (Action action : node.getActions()) {
			if (node.getPlayer() == 0) {
				sequenceIdByInformationSetAndActionChance[node.getInformationSet()].put(action.getName(),
						numSequencesNature++);
			} else if (node.getPlayer() == 1 && !visitedP1.contains(node.getInformationSet())) {
				//if(!sequenceIdByInformationSetAndActionP2[node.getInformationSet()].containsKey(action.getName()))
					sequenceIdByInformationSetAndActionP1[node.getInformationSet()].put(action.getName(), numSequencesP1++);
				if (playerToSolveFor == 1)
					primalSequenceNames[numSequencesP1 - 1] = Integer.toString(node.getInformationSet()) + ";"
							+ action.getName();
				else
					dualSequenceNames[numSequencesP1 - 1] = Integer.toString(node.getInformationSet()) + ";"
							+ action.getName();
			} else if (node.getPlayer() == 2 && !visitedP2.contains(node.getInformationSet())) {
				//if(!sequenceIdByInformationSetAndActionP2[node.getInformationSet()].containsKey(action.getName()))
					sequenceIdByInformationSetAndActionP2[node.getInformationSet()].put(action.getName(), numSequencesP2++);
				if (playerToSolveFor == 2)
					primalSequenceNames[numSequencesP2 - 1] = Integer.toString(node.getInformationSet()) + ";"
							+ action.getName();
				else
					dualSequenceNames[numSequencesP2 - 1] = Integer.toString(node.getInformationSet()) + ";"
							+ action.getName();
			}
			CreateSequenceFormIds(action.getChildId(), visitedP1, visitedP2);
		}
		if (node.getPlayer() == 1) {
			visitedP1.add(node.getInformationSet());
		} else if (node.getPlayer() == 2) {
			visitedP2.add(node.getInformationSet());
		}
	}

	/**
	 * Creates sequence form variables in pre-order traversal. A constraint is also
	 * added to ensure that the probability sum over the new sequences sum to the
	 * value of the last seen sequence on the path to this information set
	 * 
	 * @param currentNodeId
	 * @param parentSequence
	 *            last seen sequence belonging to the primal player
	 * @param visited
	 *            keeps track of which information sets have been visited
	 * @throws IloException
	 */
	private void CreateSequenceFormVariablesAndConstraints(int currentNodeId, int primalSequeceId, int dualSequeceId, IloNumVar parentSequence, String childSequence, TIntSet visited,
			TIntSet opponentVisited, double natureProbability, int infoset) throws IloException {
		Node node = game.getNodeById(currentNodeId);
		if (null == node)
			return;

		if (node.isLeaf()) { // Objective function
			double value = playerToSolveFor == player1 ? node.getPlayerOneValue() : node.getPlayerTwoValue();
			
			if (modelStrategyVars[dualSequeceId].containsKey(primalSequeceId)) {
				p1PayoffMatrix[dualSequeceId].put(primalSequeceId, (p1PayoffMatrix[dualSequeceId].get(primalSequeceId)+(value*natureProbability)));
				//System.out.println("Z:" +z );
			} else {
			    p1PayoffMatrix[dualSequeceId].put(primalSequeceId,value*natureProbability);
			    modelStrategyVars[dualSequeceId].put(primalSequeceId,childSequence);
			}
			
			return;
		}

		if (node.getPlayer() == playerToSolveFor && !visited.contains(node.getInformationSet())) {
			visited.add(node.getInformationSet());
			IloLinearNumExpr sum = cplex.linearNumExpr();
			for (Action action : node.getActions()) {
				// real-valued variable in (0,1)

				//IloNumVar v = cplex.numVar(0, 1, IloNumVarType.Int, "I:" + node.getInformationSet() + "  action:" + action.getName());
				IloNumVar v = cplex.numVar(0, 1, "I:" + node.getInformationSet() + "  action:" + action.getName());
				strategyVarsByInformationSet[node.getInformationSet()].put(action.getName(), v);
				int sequenceId = getSequenceIdForPlayerToSolveFor(node.getInformationSet(), action.getName());
				strategyVarsBySequenceId[sequenceId] = v;
				p2InformationSetBySequenceId[sequenceId] = node.getInformationSet();
				// add 1*v to the sum over all the sequences at the information set
				sum.addTerm(1, v);
				//natureConstraints.addTerm(1, v);
				CreateSequenceFormVariablesAndConstraints(action.getChildId(),sequenceId, dualSequeceId, v, childSequence, visited, opponentVisited,
						natureProbability,node.getInformationSet());
			}

			
			primalConstraints.put(node.getInformationSet(),
					cplex.addEq(sum, parentSequence, "Primal" + node.getInformationSet()));
			//System.out.println("Sum : " + sum + " = " + 1);
			
		} else if (node.getPlayer() == playerNotToSolveFor && !opponentVisited.contains(node.getInformationSet())) {
			opponentVisited.add(node.getInformationSet());
			IloLinearNumExpr sum = cplex.linearNumExpr();
			for (Action action : node.getActions()) {
				// real-valued variable in (0,1) 
				String v = "";
				int sequenceId = getSequenceIdForPlayerNotToSolveFor(node.getInformationSet(), action.getName());
				//System.out.println( action + " Sequecne id : " + sequenceId);

				if (!opponentStrategyVarsByInformationSet[node.getInformationSet()].containsKey(action.getName())) {
					v = "I:" + node.getInformationSet() + "  action:" + action.getName();
					opponentStrategyVarsByInformationSet[node.getInformationSet()].put(action.getName(), v);
					opponentStrategyVarsBySequenceId[sequenceId] = v;
					p2InformationSetBySequenceId[sequenceId] = node.getInformationSet();
					// add 1*v to the sum over all the sequences at the information set
					
				} else {
				    v = opponentStrategyVarsByInformationSet[node.getInformationSet()].get(action.getName());
				}
				CreateSequenceFormVariablesAndConstraints(action.getChildId(),primalSequeceId, sequenceId, parentSequence, v, visited,
						opponentVisited, natureProbability,node.getInformationSet());
			}
			
		} 
		
		else {
			for (Action action : node.getActions()) {

				if (null != action) {
					int newPrimalSequence = node.getPlayer() == playerToSolveFor
							? getSequenceIdForPlayerToSolveFor(node.getInformationSet(), action.getName())
							: primalSequeceId;
					int newDualSequence = node.getPlayer() == playerNotToSolveFor
							? getSequenceIdForPlayerNotToSolveFor(node.getInformationSet(), action.getName())
							: dualSequeceId;
					double newNatureProbability = node.getPlayer() == 0 ? natureProbability * action.getProbability()
							: natureProbability;
					//System.out.println(action + " Prob: " + newNatureProbability);
					if (node.getPlayer() == playerToSolveFor) {
						// update parentSequence to be the current sequence
						IloNumVar v = strategyVarsByInformationSet[node.getInformationSet()].get(action.getName());
						if (null != action) {

							CreateSequenceFormVariablesAndConstraints(action.getChildId(),newPrimalSequence, newDualSequence,v, childSequence,visited, opponentVisited,
									newNatureProbability,node.getInformationSet());
						}
					} else if (node.getPlayer() == playerNotToSolveFor) {
						String v = opponentStrategyVarsByInformationSet[node.getInformationSet()].get(action.getName());
						if (null != action) {
							CreateSequenceFormVariablesAndConstraints(action.getChildId(), newPrimalSequence,newDualSequence, parentSequence, v,visited, opponentVisited,
									newNatureProbability,node.getInformationSet());
						}
						
					} else {
						if (null != action) {
					
							CreateSequenceFormVariablesAndConstraints(action.getChildId(),newPrimalSequence,newPrimalSequence, parentSequence, childSequence, visited,
									opponentVisited, newNatureProbability,node.getInformationSet());
						}
					}
				}
			}
		}
	}

	private void CreateDualVariablesAndConstraints() throws IloException {
		
		int numVars = 0;
		int otherPlayerNumVars = 0;
		if (playerToSolveFor == 1) {
			numVars = game.getNumInformationSetsPlayer2() + 1;
			otherPlayerNumVars = game.getNumInformationSetsPlayer1() + 1;
		} else {
			numVars = game.getNumInformationSetsPlayer1() + 1;
			otherPlayerNumVars = game.getNumInformationSetsPlayer2() + 1;
		}
		String[] names = new String[numVars];
		for (int i = 0; i < numVars; i++) {
			names[i] = "Y" + i;
		}
		this.dualVars = cplex.numVarArray(numVars, -Double.MAX_VALUE, Utils.PLAYER_ONE_MAX_VAL, names);

		InitializeDualSequenceMatrix();
		InitializeDualPayoffMatrix();
	    System.out.println("***************************************** Equation No 2 ************************************************");
		
	   // System.out.println("numSequencesP2 : " + numSequencesP2);
	    for (int sequenceId = 1; sequenceId < numSequencesP2; sequenceId += Utils.MAX_NO_ATTACKER_ACTIONS) {

			CreateDualConstraintForSequence(sequenceId);
		}

	}

	private void InitializeDualSequenceMatrix() throws IloException {
		sequenceFormDualMatrix[0].add(0);
		InitializeDualSequenceMatrixRecursive(game.getRoot(), new TIntHashSet(), 0, 1);
	}

	private void InitializeDualSequenceMatrixRecursive(int currentNodeId, TIntSet visited, int parentSequenceId,
			double natureProbability) throws IloException {
		Node node = this.game.getNodeById(currentNodeId);

		if (null == node || node.isLeaf())
			return;

		if (playerNotToSolveFor == node.getPlayer() && !visited.contains(node.getInformationSet())) {
			visited.add(node.getInformationSet());
			int informationSetMatrixId = node.getInformationSet();// +
																	// (1-game.getSmallestInformationSetId(playerNotToSolveFor));
																	// // map information set ID to 1 indexing. Assumes
																	// that information sets are named by consecutive
																	// integers
			sequenceFormDualMatrix[parentSequenceId].add(informationSetMatrixId);
			// sequenceFormDualProbMatrix[parentSequenceId].put(parentSequenceId,
			// natureProbability);
			for (Action action : node.getActions()) {
				if (null != action) {
					int newSequenceId = getSequenceIdForPlayerNotToSolveFor(node.getInformationSet(), action.getName());
					sequenceFormDualMatrix[newSequenceId].add(informationSetMatrixId);
					InitializeDualSequenceMatrixRecursive(action.getChildId(), visited, newSequenceId,
							natureProbability);
				}
			}
		} else {
			for (Action action : node.getActions()) {

				if (null != action) {
					int newSequenceId = playerNotToSolveFor == node.getPlayer()
							? getSequenceIdForPlayerNotToSolveFor(node.getInformationSet(), action.getName())
							: parentSequenceId;
					double newNatureProbability = node.getPlayer() == 0 ? natureProbability * action.getProbability()
							: natureProbability;
					InitializeDualSequenceMatrixRecursive(action.getChildId(), visited, newSequenceId,
							newNatureProbability);
				}
			}
		}

	}

	private void InitializeDualPayoffMatrix() throws IloException {

		InitializeDualPayoffMatrixRecursive(game.getRoot(), 0, 0, 1); // Start with the root sequences

	}

	private void InitializeDualPayoffMatrixRecursive(int currentNodeId, int primalSequence, int dualSequence,
			double natureProbability) throws IloException {
		
		Node node = this.game.getNodeById(currentNodeId);
		if (null == node)
			return;
		if (node.isLeaf()) {
			double valueMultiplier = playerNotToSolveFor == 1 ? node.getPlayerOneValue() : node.getPlayerTwoValue();
			double leafValue = (natureProbability*valueMultiplier);
			if (dualPayoffMatrix[dualSequence].containsKey(primalSequence)) {
				dualPayoffMatrix[dualSequence].put(primalSequence,
						(dualPayoffMatrix[dualSequence].get(primalSequence) + leafValue));
				symmetricActionCntInP2InformationSet[dualSequence].put(primalSequence,
						(symmetricActionCntInP2InformationSet[dualSequence].get(primalSequence) + 1));
			} else {
				dualPayoffMatrix[dualSequence].put(primalSequence, leafValue);
				symmetricActionCntInP2InformationSet[dualSequence].put(primalSequence, 1);
				
			}
			sequenceFormDualProbMatrix[dualSequence].put(primalSequence, natureProbability);

		} else {
			for (Action action : node.getActions()) {
				if (action != null) {
					int newPrimalSequence = node.getPlayer() == playerToSolveFor
							? getSequenceIdForPlayerToSolveFor(node.getInformationSet(), action.getName())
							: primalSequence;
					int newDualSequence = node.getPlayer() == playerNotToSolveFor
							? getSequenceIdForPlayerNotToSolveFor(node.getInformationSet(), action.getName())
							: dualSequence;
					double newNatureProbability = node.getPlayer() == 0 ? natureProbability * action.getProbability()
							: natureProbability;
					//System.out.println("Primal Seq " + newDualSequence );
					InitializeDualPayoffMatrixRecursive(action.getChildId(), newPrimalSequence, newDualSequence,
							newNatureProbability);
				}
			}
		}
	}

	private void CreateDualConstraintForSequence(int sequenceId) throws IloException {
		

		double expectedValue = - Utils.PLAYER_ONE_MAX_VAL;
		String actionKey = "";
		for (int actionNo = 0; actionNo < Utils.MAX_NO_ATTACKER_ACTIONS; actionNo++) {
			int tmpIndex = sequenceId + actionNo;
			double totalActionPayoff = 0.0;
			if (dualPayoffMatrix[tmpIndex].size() > 0) {
				TIntDoubleIterator it = dualPayoffMatrix[tmpIndex].iterator();
				TIntObjectIterator<String> itt1 = modelStrategyVars[tmpIndex].iterator();
				TIntDoubleIterator itt2 = symmetricActionCntInP2InformationSet[tmpIndex].iterator();
				for (int i = dualPayoffMatrix[tmpIndex].size(); i-- > 0;) {
					it.advance();
					itt1.advance();
					itt2.advance();
					double  totValue = it.value()/itt2.value();
					totalActionPayoff += totValue;
				

				}
				//System.out.println(opponentStrategyVarsBySequenceId[tmpIndex] + " : " + totalActionPayoff);
				if(totalActionPayoff > expectedValue) {
					expectedValue = totalActionPayoff;
					actionKey = opponentStrategyVarsBySequenceId[tmpIndex];
					}
			}
			
		}
		opponentBrStrategy.put(actionKey, true);
		System.out.println("St solver : " + actionKey + " = 1");
		
	
	}

	/**
	 * Fills in the convenience arrays nodeNatureProbabilities and
	 * sequenceIdForNodeP1/2
	 */
	void computeAuxiliaryInformationForNodes() {
		computeAuxiliaryInformationForNodesRecursive(game.getRoot(), 0, 0, 1);
	}

	private void computeAuxiliaryInformationForNodesRecursive(int currentNodeId, int sequenceIdP1, int sequenceIdP2,
			double natureProbability) {
		Node node = this.game.getNodeById(currentNodeId);

		nodeNatureProbabilities[node.getNodeId()] = natureProbability;
		sequenceIdForNodeP1[currentNodeId] = sequenceIdP1;
		sequenceIdForNodeP2[currentNodeId] = sequenceIdP2;
		if (node.isLeaf())
			return;

		for (Action action : node.getActions()) {
			int newSequenceIdP1 = node.getPlayer() == 1
					? sequenceIdByInformationSetAndActionP1[node.getInformationSet()].get(action.getName())
					: sequenceIdP1;
			int newSequenceIdP2 = node.getPlayer() == 2
					? sequenceIdByInformationSetAndActionP2[node.getInformationSet()].get(action.getName())
					: sequenceIdP2;
			double newNatureProbability = node.getPlayer() == 0 ? natureProbability * action.getProbability()
					: natureProbability;
			computeAuxiliaryInformationForNodesRecursive(action.getChildId(), newSequenceIdP1, newSequenceIdP2,
					newNatureProbability);
		}
	}

	int getSequenceIdForPlayerNature(int informationSet, String actionName) {
		return sequenceIdByInformationSetAndActionChance[informationSet].get(actionName);

	}

	int getSequenceIdForPlayerToSolveFor(int informationSet, String actionName) {
		if (playerToSolveFor == 1) {
			return sequenceIdByInformationSetAndActionP1[informationSet].get(actionName);
		} else {
			return sequenceIdByInformationSetAndActionP2[informationSet].get(actionName);
		}
	}

	int getSequenceIdForPlayerNotToSolveFor(int informationSet, String actionName) {
		if (playerNotToSolveFor == 1) {
			return sequenceIdByInformationSetAndActionP1[informationSet].get(actionName);
		} else {
			return sequenceIdByInformationSetAndActionP2[informationSet].get(actionName);
		}
	}

	private void SetObjective() throws IloException {
	for (int sequenceId = 1; sequenceId < numSequencesP2; sequenceId++) {

			TIntDoubleIterator it = p1PayoffMatrix[sequenceId].iterator();
			TIntObjectIterator<String> itt1 = modelStrategyVars[sequenceId].iterator();
			TIntDoubleIterator itt2 = symmetricActionCntInP2InformationSet[sequenceId].iterator();

			for (int i = p1PayoffMatrix[sequenceId].size(); i-- > 0;) {
				it.advance();
				itt1.advance();
				itt2.advance();
				double totValue =0.0;
				if(opponentBrStrategy.containsKey(itt1.value()))
					totValue = it.value() / itt2.value();
				objective.addTerm(totValue, strategyVarsBySequenceId[it.key()]);
			}

			
		}
		cplex.addMaximize(objective);
		System.out.println("************************************************ Equation no 1 ***************************");
		System.out.println("Objective Function  StackelBerg: " + objective);
	}

	public int getPlayerToSolveFor() {
		return playerToSolveFor;
	}

	public int getPlayerNotToSolveFor() {
		return playerNotToSolveFor;
	} 

	public IloCplex getCplex() {
		return cplex;
	}

	public IloNumVar[] getDualVars() {
		return dualVars;
	}

	public HashMap<String, IloNumVar>[] getStrategyVarsByInformationSet() {
		return strategyVarsByInformationSet;
	}

	public TIntList[] getSequenceFormDualMatrix() {
		return sequenceFormDualMatrix;
	}

	public TIntDoubleMap[] getDualPayoffMatrix() {
		return dualPayoffMatrix;
	}

	public TObjectIntMap<String>[] getSequenceIdByInformationSetAndActionP1() {
		return sequenceIdByInformationSetAndActionP1;
	}

	public TObjectIntMap<String>[] getSequenceIdByInformationSetAndActionP2() {
		return sequenceIdByInformationSetAndActionP2;
	}

	public IloNumVar[] getStrategyVarsBySequenceId() {
		return strategyVarsBySequenceId;
	}

	public int getNumSequencesP1() {
		return numSequencesP1;
	}

	public int getNumSequencesP2() {
		return numSequencesP2;
	}

	public int getNumPrimalSequences() {
		return numPrimalSequences;
	}

	public int getNumDualSequences() {
		return numDualSequences;
	}

	public TIntObjectMap<IloConstraint> getPrimalConstraints() {
		return primalConstraints;
	}

	public TIntObjectMap<IloRange> getDualConstraints() {
		return dualConstraints;
	}

	@Override
	public double[][][] getStrategyProfile() {
		double[][][] profile = new double[3][][];
		System.out.println("Number of sequece " + numSequencesP1);
		profile[playerToSolveFor] = new double[numSequencesP1+1][];
		for (int informationSetId = 0; informationSetId < numSequencesP1; informationSetId++) {
			
			profile[playerToSolveFor][informationSetId] = new double[game
					.getNumActionsAtInformationSet(playerToSolveFor, informationSetId)];
			double sum = 0;
			for (String actionName : strategyVarsByInformationSet[informationSetId].keySet()) {
				try {
					sum += cplex.getValue(strategyVarsByInformationSet[informationSetId].get(actionName));

				} catch (IloException e) {
					e.printStackTrace();
				}
			}

			for (int actionId = 0; actionId < game.getNumActionsAtInformationSet(playerToSolveFor,
					informationSetId); actionId++) {
				String actionName = game.getActionsAtInformationSet(playerToSolveFor, informationSetId)[actionId]
						.getName();
				try {
					if (sum > 0) {
						profile[playerToSolveFor][informationSetId][actionId] = cplex
								.getValue(strategyVarsByInformationSet[informationSetId].get(actionName));
					} else {
						profile[playerToSolveFor][informationSetId][actionId] = 1.0
								/ game.getNumActionsAtInformationSet(playerToSolveFor, informationSetId);
					}
					/*
					 * if (profile[playerToSolveFor][informationSetId][actionId] > 0.00005) { cost
					 * += (tempModificationCost[actionId]
					 * profile[playerToSolveFor][informationSetId][actionId]); prob +=
					 * profile[playerToSolveFor][informationSetId][actionId]; }
					 */
					 System.out.println(strategyVarsByInformationSet[informationSetId].get(
					 actionName) + " : " + profile[playerToSolveFor][informationSetId][actionId]);
					 
				} catch (IloException e) {
					e.printStackTrace();
				}
			}
		}
		return profile;
	}
}
