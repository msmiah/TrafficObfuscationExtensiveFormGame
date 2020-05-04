package extensive_form_game_solver;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.omg.CORBA.SystemException;

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

public class DoubleOracleLPSolver<E> extends ZeroSumGameSolver {
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
	HashMap<String, IloNumVar>[] opponentStrategyVarsByInformationSet; // indexed as [inforationSetId][action.name]
	HashMap<String, Integer>[] p2SymmetricActionNumByInformationSet;

	TIntList[] sequenceFormDualMatrix; // indexed as [dual sequence id][information set]
	TIntDoubleMap[] sequenceFormDualProbMatrix;
	TIntDoubleMap[] sequenceFormDualP1Matrix;
	TIntDoubleMap[] dualPayoffMatrix; // indexed as [dual sequence][primal sequence]
	TIntDoubleMap[] p1PayoffMatrix;
	TIntDoubleMap[] symmetricActionCntInP2InformationSet;
	TIntObjectMap<IloNumVar>[] modelStrategyVars;
	TObjectIntMap<String>[] sequenceIdByInformationSetAndActionChance;
	TObjectIntMap<String>[] sequenceIdByInformationSetAndActionP1; // indexed as [informationSetId][action.name]
	TObjectIntMap<String>[] sequenceIdByInformationSetAndActionP2; // indexed as [informationSetId][action.name]
	IloNumVar[] strategyVarsBySequenceId;
	IloNumVar[] opponentStrategyVarsBySequenceId;
	IloNumVar[] zVarsBySequenceId;
	private int[][] restictedInformationSet; 
	private int[][][] actionRestrictionMapping;
	@SuppressWarnings("unchecked")
	private HashMap<String, Integer>[][] restrictedInformationSetIdToActions = new HashMap[3][];
	
	
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

	public DoubleOracleLPSolver(Game game, int playerToSolveFor) {
		this(game, playerToSolveFor, 1e-6);
	}

	public DoubleOracleLPSolver(Game game, int playerToSolveFor, double tol) {
		super(game);
		this.game = game;
		this.playerToSolveFor = playerToSolveFor;
		this.playerNotToSolveFor = (playerToSolveFor % 2) + 1;
		initializeRestrictedGameDataStructure();
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
		this.opponentStrategyVarsByInformationSet = (HashMap<String, IloNumVar>[]) new HashMap[opponentNumInformationSets
				+ 1];
		this.p2SymmetricActionNumByInformationSet = (HashMap<String, Integer>[]) new HashMap[opponentNumInformationSets
		                                                                       				+ 1];
		
		for (int i = 0; i <= numInformationSets; i++) {
			this.strategyVarsByInformationSet[i] = new HashMap<String, IloNumVar>();
		}

		for (int i = 0; i <= opponentNumInformationSets; i++) {
			this.opponentStrategyVarsByInformationSet[i] = new HashMap<String, IloNumVar>();
			this.p2SymmetricActionNumByInformationSet[i] = new HashMap<String, Integer>();
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
			opponentStrategyVarsBySequenceId = new IloNumVar[game.getNumSequencesP2()];
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

	private void initializeRestrictedGameDataStructure() {
		int numInformationSets = 0;
		int opponentNumInformationSets = 0;

		if (playerToSolveFor == 1) {
			numInformationSets = game.getNumInformationSetsPlayer1();
			opponentNumInformationSets = game.getNumInformationSetsPlayer2();
		} else {
			numInformationSets = game.getNumInformationSetsPlayer2();
			opponentNumInformationSets = game.getNumInformationSetsPlayer1();
		}
		restictedInformationSet = new int[3][];
		restictedInformationSet[1] = new int[numInformationSets];
		restictedInformationSet[2]= new int[opponentNumInformationSets];
		

		restrictedInformationSetIdToActions[1] = (HashMap<String, Integer>[]) new HashMap[numInformationSets + 1];
		restrictedInformationSetIdToActions[2] = (HashMap<String, Integer>[]) new HashMap[opponentNumInformationSets + 1];
		
		for (int i = 0; i <= numInformationSets; i++) {
			this.restrictedInformationSetIdToActions[1][i] = new HashMap<String, Integer>();
		}
		
		for (int i = 0; i <= opponentNumInformationSets; i++) {
			this.restrictedInformationSetIdToActions[2][i] = new HashMap<String, Integer>();
		}

		/*
		actionRestrictionMapping = new int[3][][];
		actionRestrictionMapping[1] = new int[numPrimalSequences][];
		actionRestrictionMapping[2] = new int[numDualSequences][];*/
		
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
				System.out.println("Defender's utility : " + valueOfGame);
			}else {
				System.out.println("Game is not Solveable" );
			}

		} catch (IloException e) {
			e.printStackTrace();
			System.out.println("Error SequenceFormLPSolver::solveGame: solve exception");
		}
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
			fw.write("...............Attacker's strategy................\n");
			
			for (IloNumVar v : opponentStrategyVarsBySequenceId) {
				if (v != null)
					//cplex.add(v);
					//System.out.println(v);

					if (cplex.getValue(v) < 0.00005)
						fw.write(v.getName() + ": \t" + 0.0 + "\n");
					else
						fw.write(v.getName() + ": \t" + cplex.getValue(v) + "\n");
			}
			
			fw.write("............... Z variables................\n");
			
			for (IloNumVar v : zVarsBySequenceId) {
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
		try {
			cplex = new IloCplex();
		} catch (IloException e) {
			System.out.println("Error SequenceFormLPSolver(): CPLEX setup failed");
		}

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
		CreateSequenceFormVariablesAndConstraints(game.getRoot(),0,0, rootSequence, rootSequence, new TIntHashSet(), new TIntHashSet(),
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
				if (!sequenceIdByInformationSetAndActionP2[node.getInformationSet()].containsKey(action.getName()))
					p2SymmetricActionNumByInformationSet[node.getInformationSet()].put(action.getName(), 1);
				else
					p2SymmetricActionNumByInformationSet[node.getInformationSet()].put(action.getName(),
							p2SymmetricActionNumByInformationSet[node.getInformationSet()].get(action.getName()) + 1);
				
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
	private void CreateSequenceFormVariablesAndConstraints(int currentNodeId, int primalSequeceId, int dualSequeceId, IloNumVar parentSequence, IloNumVar childSequence, TIntSet visited,
			TIntSet opponentVisited, double natureProbability, int infoset) throws IloException {
		Node node = game.getNodeById(currentNodeId);
		if (null == node)
			return;

		if (node.isLeaf()) { // Objective function
			double value = playerToSolveFor == player1 ? node.getPlayerOneValue() : node.getPlayerTwoValue();
			
			//System.out.println(childSequence + " : " + value);
			/* Linearizing constraints*/

			IloLinearNumExpr lz1 = cplex.linearNumExpr();
			IloLinearNumExpr lz2 = cplex.linearNumExpr();
			IloLinearNumExpr lz3 = cplex.linearNumExpr();
			//IloNumVar z = cplex.numVar(0, 1, parentSequence+" -> "+childSequence);
			
			IloNumVar z ;
			if (modelStrategyVars[dualSequeceId].containsKey(primalSequeceId)) {
				z = modelStrategyVars[dualSequeceId].get(primalSequeceId);
				p1PayoffMatrix[dualSequeceId].put(primalSequeceId, (p1PayoffMatrix[dualSequeceId].get(primalSequeceId)+(value*natureProbability)));
				//System.out.println("Z:" +z );
			} else {
				z = cplex.numVar(0, 1, parentSequence +" -> "+ childSequence);
			    
			    /*z-A <= 0 upper bound is 1*/
				lz1.addTerm(1, z);
				lz1.addTerm(-1, parentSequence);
				primalConstraints.put(node.getInformationSet(),
						cplex.addLe(lz1, 0, "TLZ1" + dualSequeceId));
				
				/*Z-A+x<=1 */
				/*
				lz1.addTerm(1, childSequence);
				primalConstraints.put(node.getInformationSet(),
						cplex.addLe(lz1, 1, "TLZ1" + node.getInformationSet()));
				*/
				/*z- x <= 0 */
				lz2.addTerm(1, z);
				lz2.addTerm(-1, childSequence);
				primalConstraints.put(node.getInformationSet(),
						cplex.addLe(lz2, 0, "TLZ2" + dualSequeceId));
				
				//System.out.println("lz2: " + lz2);
				
				/*A+x-Z <= 1*/
				lz3.addTerm(-1, z);
				lz3.addTerm(1, parentSequence);
				lz3.addTerm(1, childSequence);
				//System.out.println(lz3);
				primalConstraints.put(node.getInformationSet(),
						cplex.addLe(lz3, 1, "TLZ3" + dualSequeceId));

			    modelStrategyVars[dualSequeceId].put(primalSequeceId,z);
			    p1PayoffMatrix[dualSequeceId].put(primalSequeceId,value*natureProbability);
			    zVarsBySequenceId[primalSequeceId] = z;
			}
			
			
		   // System.out.println(parentSequence + "->" + childSequence + " : " +value);
		    //objective.addTerm(value*natureProbability, z);
			//System.out.println("********************************* Equation no 1 **************************************");
			//System.out.println("Objective :" + objective);
			return;
		}

		if (node.getPlayer() == playerToSolveFor && !visited.contains(node.getInformationSet())) {
			visited.add(node.getInformationSet());
			IloLinearNumExpr sum = cplex.linearNumExpr();
			for (Action action : node.getActions()) {
				
				if(!restrictedInformationSetIdToActions[node.getPlayer()][node.getInformationSet()].containsKey(action.getName()))
					continue;
				// real-valued variable in (0,1)
				
				//IloNumVar v = cplex.numVar(0, 1, IloNumVarType.Int, "I:" + node.getInformationSet() + "  action:" + action.getName());
				IloNumVar v = cplex.numVar(0, 1, "I:" + node.getInformationSet() + "  action:" + action.getName());
				strategyVarsByInformationSet[node.getInformationSet()].put(action.getName(), v);
				int sequenceId = getSequenceIdForPlayerToSolveFor(node.getInformationSet(), action.getName());
				strategyVarsBySequenceId[sequenceId] = v;
				p2InformationSetBySequenceId[sequenceId] = node.getInformationSet();
				// add 1*v to the sum over all the sequences at the information set
				sum.addTerm(1, v);
				natureConstraints.addTerm(1, v);
				CreateSequenceFormVariablesAndConstraints(action.getChildId(),sequenceId, dualSequeceId, v, childSequence, visited, opponentVisited,
						natureProbability,node.getInformationSet());
			}

			
			primalConstraints.put(node.getInformationSet(),
					cplex.addEq(sum, parentSequence, "Primal" + node.getInformationSet()));
			System.out.println("Sum : " + sum + " = " + 1);
			
		} else if (node.getPlayer() == playerNotToSolveFor && !opponentVisited.contains(node.getInformationSet())) {
			opponentVisited.add(node.getInformationSet());
			IloLinearNumExpr sum = cplex.linearNumExpr();
			for (Action action : node.getActions()) {
				// real-valued variable in (0,1) 
				if(!restrictedInformationSetIdToActions[node.getPlayer()][node.getInformationSet()].containsKey(action.getName()))
					continue;
				IloNumVar v = null;
				int sequenceId = getSequenceIdForPlayerNotToSolveFor(node.getInformationSet(), action.getName());
				//System.out.println( action + " Sequecne id : " + sequenceId);

				if (!opponentStrategyVarsByInformationSet[node.getInformationSet()].containsKey(action.getName())) {
					v = cplex.numVar(0, 1, IloNumVarType.Bool,
							"I:" + node.getInformationSet() + "  action:" + action.getName());
					opponentStrategyVarsByInformationSet[node.getInformationSet()].put(action.getName(), v);
					//p2SymmetricActionNumByInformationSet[node.getInformationSet()].put(action.getName(), 1);
					opponentStrategyVarsBySequenceId[sequenceId] = v;
					p2InformationSetBySequenceId[sequenceId] = node.getInformationSet();
					// add 1*v to the sum over all the sequences at the information set
					sum.addTerm(1, v);
					
				} else {
				    v = opponentStrategyVarsByInformationSet[node.getInformationSet()].get(action.getName());
				  //  p2SymmetricActionNumByInformationSet[node.getInformationSet()].put(action.getName(), 
				  //  		p2SymmetricActionNumByInformationSet[node.getInformationSet()].get(action.getName())+1);
				}
				CreateSequenceFormVariablesAndConstraints(action.getChildId(),primalSequeceId, sequenceId, parentSequence, v, visited,
						opponentVisited, natureProbability,node.getInformationSet());
			}

			primalConstraints.put(node.getInformationSet(),
				cplex.addEq(sum,1, "P2" + node.getInformationSet()));
			System.out.println("Sum P2: " + sum + " = " + 1);
			
		} 
		
		else {
			for (Action action : node.getActions()) {

				if (null != action) {

					if(node.getPlayer() !=0 && !restrictedInformationSetIdToActions[node.getPlayer()][node.getInformationSet()].containsKey(action.getName()))
						continue;
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
						IloNumVar v = opponentStrategyVarsByInformationSet[node.getInformationSet()].get(action.getName());
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
					if(node.getPlayer() !=0  && 
						!restrictedInformationSetIdToActions[node.getPlayer()][node.getInformationSet()].containsKey(action.getName()))
						continue;
					
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
		

      //int p2InformationSet = p2InformationSetBySequenceId[sequenceId];
      //int numOfActionsInInformationSet = opponentStrategyVarsByInformationSet[p2InformationSet].size();

        /* lhs is linear expression of expected payoff in each information set*/
		IloLinearNumExpr lhs = cplex.linearNumExpr();
		for (int actionNo = 0; actionNo < Utils.MAX_NO_ATTACKER_ACTIONS; actionNo++) {
			int tmpIndex = sequenceId + actionNo;
			TIntDoubleIterator it = dualPayoffMatrix[tmpIndex].iterator();
			TIntObjectIterator<IloNumVar> itt1 = modelStrategyVars[tmpIndex].iterator();
			TIntDoubleIterator itt2 = symmetricActionCntInP2InformationSet[tmpIndex].iterator();
			for (int i = dualPayoffMatrix[tmpIndex].size(); i-- > 0;) {
				it.advance();
				itt1.advance();
				itt2.advance();
				double  totValue = it.value()/itt2.value();
				//System.out.println(itt2.value());
				lhs.addTerm(totValue, itt1.value());
			}
		}
		
		for (int actionNo = 0; actionNo < Utils.MAX_NO_ATTACKER_ACTIONS; actionNo++) {
			int tmpIndex = sequenceId + actionNo;
			IloLinearNumExpr rhs  = null;
			if (dualPayoffMatrix[tmpIndex].size() > 0) {
				rhs = cplex.linearNumExpr();
				TIntDoubleIterator it = dualPayoffMatrix[tmpIndex].iterator();
				TIntObjectIterator<IloNumVar> itt1 = modelStrategyVars[tmpIndex].iterator();
				TIntDoubleIterator itt2 = symmetricActionCntInP2InformationSet[tmpIndex].iterator();
				for (int i = dualPayoffMatrix[tmpIndex].size(); i-- > 0;) {
					it.advance();
					itt1.advance();
					itt2.advance();
					double  totValue = it.value()/itt2.value();
					 //rhs.addTerm(totValue, opponentStrategyVarsBySequenceId[tmpIndex]);					
					//rhs.addTerm(totValue, itt1.value());
					rhs.addTerm(totValue, strategyVarsBySequenceId[it.key()]);
				}
				System.out.println(rhs);
				if(rhs != null)	
					cplex.addGe(lhs,rhs, "Dual" + tmpIndex);
			}
		}
		//System.out.println(lhs);
		
	
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
			TIntObjectIterator<IloNumVar> itt1 = modelStrategyVars[sequenceId].iterator();
			TIntDoubleIterator itt2 = symmetricActionCntInP2InformationSet[sequenceId].iterator();
			for (int i = p1PayoffMatrix[sequenceId].size(); i-- > 0;) {
				it.advance();
				itt1.advance();
				itt2.advance();
				double totValue = it.value() / itt2.value();
				objective.addTerm(totValue, itt1.value());
			}

			
		}
		
		cplex.addMaximize(objective);
		System.out.println("************************************************ Equation no 1 ***************************");
		System.out.println("Objective Function : " + objective);
	}

	public void solveRestrictedGame() throws IloException
	{
		initializeDataStructures();
		setUpModel(1e-6);
	}
	
	public void updateRestrictedGame(int currentNodeId, TObjectDoubleMap<String>[] brSequences,TIntSet visited,
			TIntSet opponentVisited) throws IloException {

		Node node = game.getNodeById(currentNodeId);
		if (node.isLeaf()) {
			return;
		}
		
		if (node.getPlayer() == playerToSolveFor &&  !visited.contains(node.getInformationSet())) {
			visited.add(node.getInformationSet());
			for (Action action : node.getActions()) {
				String v = "I:" + node.getInformationSet() + " action:" + action.getName();
				if(brSequences[node.getPlayer()].containsKey(v)
						&& !restrictedInformationSetIdToActions[node.getPlayer()][node.getInformationSet()].containsKey(action.getName())) {
					
					restictedInformationSet[node.getPlayer()][node.getInformationSet()] = node.getInformationSet();
					restrictedInformationSetIdToActions[node.getPlayer()][node.getInformationSet()].put(action.getName(), node.getInformationSet());
					//System.out.println(node.getInformationSet()+ " : " + action.getName());
				}else if(!restrictedInformationSetIdToActions[node.getPlayer()][node.getInformationSet()].containsKey(action.getName())) {
						continue;
				} 

				System.out.println( " Restricted sequences I: " + node.getInformationSet() + " action:"+action.getName());
					updateRestrictedGame(action.getChildId(),brSequences, visited, opponentVisited);
			}
		} else if (node.getPlayer() == playerNotToSolveFor &&  !opponentVisited.contains(node.getInformationSet())) {
			opponentVisited.add(node.getInformationSet());
			for (Action action : node.getActions()) {
				String v = "I:" + node.getInformationSet() + " action:" + action.getName();
				
					if(brSequences[node.getPlayer()].containsKey(v) && !restrictedInformationSetIdToActions[node.getPlayer()][node.getInformationSet()].containsKey(action.getName())) {
						//System.out.println(node.getInformationSet()+ " : " + action.getName());
						restictedInformationSet[node.getPlayer()][node.getInformationSet()] = node.getInformationSet();
						restrictedInformationSetIdToActions[node.getPlayer()][node.getInformationSet()].put(action.getName(), node.getInformationSet());
					}else if(!restrictedInformationSetIdToActions[node.getPlayer()][node.getInformationSet()].containsKey(action.getName())) {
							continue;
					}
					//System.out.println( " Restricted sequences I: " + node.getInformationSet() + " action:"+action.getName());
					updateRestrictedGame(action.getChildId(),brSequences, visited, opponentVisited);
			}
		} 
		
		else {
			for (int actionId = 0; actionId < node.getActions().length; actionId++) {
				Action action = node.getActions()[actionId];
				updateRestrictedGame(action.getChildId(), brSequences, visited, opponentVisited);
				
			}
		}
	
		
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
	
	public HashMap<String, IloNumVar>[] getOpponetStrategyVarsByInformationSet() {
		return opponentStrategyVarsByInformationSet;
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
		int numSequences = 0;
		for (int player = 1; player < 3; player++) {
			numSequences= player ==1 ? numSequencesP1 : numSequencesP2;
			HashMap<String, IloNumVar>[] strategyVarsByInfoset = player == 1 ? getStrategyVarsByInformationSet() : getOpponetStrategyVarsByInformationSet();
			profile[player] = new double[numSequences + 1][];
			for (int informationSetId = 0; informationSetId < numSequences; informationSetId++) {
				boolean isDeafualtAction = true;
				String defaultActionName = null;
				profile[player][informationSetId] = new double[game
						.getNumActionsAtInformationSet(player, informationSetId)];
				double sum = 0;
				for (String actionName : strategyVarsByInfoset[informationSetId].keySet()) {
					if(!restrictedInformationSetIdToActions[player][informationSetId].containsKey(actionName))
						continue;
					try {
						sum += cplex.getValue(strategyVarsByInfoset[informationSetId].get(actionName));

					} catch (IloException e) {
						e.printStackTrace();
					}
				}

				for (int actionId = 0; actionId < game.getNumActionsAtInformationSet(player,
						informationSetId); actionId++) {
					String actionName = game.getActionsAtInformationSet(player, informationSetId)[actionId]
							.getName();
					try {
						if (sum > 0) {
							if (!restrictedInformationSetIdToActions[player][informationSetId].containsKey(actionName))
								profile[player][informationSetId][actionId] = 0;
							else {
								if (player == 2) {

									profile[player][informationSetId][actionId] = cplex
											.getValue(strategyVarsByInfoset[informationSetId].get(actionName))
											/ p2SymmetricActionNumByInformationSet[informationSetId].get(actionName);
								} else {
									System.out.println(informationSetId + " : " + actionName);
									profile[player][informationSetId][actionId] = cplex
											.getValue(strategyVarsByInfoset[informationSetId].get(actionName));
								}
							}
						} else {
							if(player == 2 && isDeafualtAction) {
							    profile[player][informationSetId][actionId] = 1.0/p2SymmetricActionNumByInformationSet[informationSetId].get(actionName);
							    isDeafualtAction = false;
							    defaultActionName = actionName;
							}
						    else if(player == 1 && isDeafualtAction) {
								profile[player][informationSetId][actionId] = 1.0;
								isDeafualtAction = false;
								defaultActionName = actionName;
						    }
							else {
								if(actionName.equals(defaultActionName) && player == 2)
									profile[player][informationSetId][actionId] = 1.0/p2SymmetricActionNumByInformationSet[informationSetId].get(actionName);
								else
									profile[player][informationSetId][actionId] = 0.0;
							}
						}
						/*
						System.out.println("I:"+informationSetId+" action:"+
								 actionName + " : " + profile[player][informationSetId][actionId]);
*/
						//System.out.println(player + " Sum :" + sum);
					} catch (IloException e) {
						e.printStackTrace();
					}
				}
			}
		}
		return profile;
	}
}
