package extensive_form_game;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.apache.commons.lang3.*;
import org.apache.commons.math3.distribution.NormalDistribution;

import au.com.bytecode.opencsv.CSVReader;
import extensive_form_game_abstraction.SignalAbstraction;
import gnu.trove.list.array.TIntArrayList;
import gnu.trove.map.TIntIntMap;
import gnu.trove.map.TObjectDoubleMap;
import gnu.trove.map.TObjectIntMap;
import gnu.trove.map.hash.TIntIntHashMap;
import gnu.trove.map.hash.TObjectIntHashMap;
import utils.Utils;

public class Game implements GameGenerator {
	
	
	public class Action {	
		private String name;
		private int childId; // id of the node lead to by taking this action
		private double probability;
		private int rem; // Legacy from zerosum package. Denotes the probability as an integer. We only use this to set the probability field
		public String getName() {
			return name;
		}
		public int getChildId() {
			return childId;
		}
		public double getProbability() {
			return probability;
		}
		
		public boolean equals(Action action) {
			if (name.equals(action.name)) return true;
			else return false;
		}
		
		@Override
		public int hashCode() {
			return name.hashCode();
		}
		@Override
		public String toString() {
			return name;
		}
	}
	public class Node {
		private int nodeId;
		private String name;
		private int player; // -2 is leaf, 0 is nature, positive integers are actual players
		private boolean publicSignal; // TODO, useful for abstraction algorithms
		private int playerReceivingSignal; // TODO, useful for abstraction algorithms
		private int informationSet;
		private int abstractInformationSet;
		private int signalGroupPlayer1; // TODO, useful for abstraction algorithms
		private int signalGroupPlayer2; // TODO, useful for abstraction algorithms
		private Action[] actions; 
		private double valuePlayerOne; // payoff at node, if node is a leaf node (player == -2) 
		private double valuePlayerTwo;
		private double value;
		public int getNodeId() {
			return nodeId;
		}
		public String getName() {
			return name;
		}
		public int getPlayer() {
			return player;
		}
		public boolean isPublicSignal() {
			return publicSignal;
		}
		public int getPlayerReceivingSignal() {
			return playerReceivingSignal;
		}
		public int getInformationSet() {
			return informationSet;
		}
		public int getRealInformationSet() {
			return informationSet;
		}
		public int getAbstractInformationSet() {
			return abstractInformationSet;
		}
		public void setAbstractInformationSet(int abstractInformationSet) {
			this.abstractInformationSet = abstractInformationSet;
		}
		public int getSignalGroupPlayer1() {
			return signalGroupPlayer1;
		}
		public int getSignalGroupPlayer2() {
			return signalGroupPlayer2;
		}
		public Action[] getActions() {
			return actions;
		}
		public double getValue() {
			return value;
		}
		public double getPlayerOneValue() {
			return valuePlayerOne;
		}
		public double getPlayerTwoValue() {
			return valuePlayerTwo;
		}
		public boolean isLeaf() {
			return player == -2;
		}
		@Override
		public String toString() {
			return name;
		}
	}
	
	int player1 = 0;
	int player2 = 1;
	int parentInfoSet;
	
	private TIntArrayList [] [] informationSets; // indexed as [player][information set]
	private boolean [] [] informationSetsSeen; // indexed as [player]
	private Node [] nodes;
	private TIntIntMap [] childNodeIdBySignalId; // indexed as [nodeId][signalId], returns the child node reached when nature selects the signal
	private TIntIntMap [] actionIdBySignalId;// indexed as [nodeId][signalId], returns the index of the signal in the action vector at the node
	@SuppressWarnings("unchecked")
	private HashMap<List<String>, Integer>[] observedActionsToInformationSetId = new HashMap[3];
	
	private int root;
	private int numChanceHistories;
	private int numCombinedPlayerHistories;
	private int numTerminalHistories;
	private int numNodes;
	private int numInformationSetsPlayer1;
	private int numInformationSetsPlayer2;
	private int smallestInformationSetId[]; // indexed as [player], keeps track of the base index for the information sets
	private int [] numSequences;
	
	private String [] signals; // TODO
	private TObjectIntMap<String> signalNameToId; // TODO signalName refers to a unique name for each signal in the set S of all signals dealt by nature. 
	private int numRounds;
	private int depth;
	private int numPrivateSignals;
	
	private double smallestPayoff;
	private double biggestPayoff;
	
	private boolean hasAbstraction;
	private int[][] abstraction; 
	private int[][][] actionAbstractionMapping;
	private HashMap<String, Double>[] systemProbability = new HashMap[2];
	private boolean useIdentityActionMap;
	SignalAbstraction signalAbstraction;
	
	public Game() {
		informationSets = new TIntArrayList [2] [];
		informationSetsSeen = new boolean [2] [];
		signalNameToId = new TObjectIntHashMap<String>();
		numSequences = new int[2];
		numSequences[0] = 1;
		numSequences[1] = 1;
		smallestInformationSetId = new int[2];
		smallestInformationSetId[0] = Integer.MAX_VALUE;
		smallestInformationSetId[1] = Integer.MAX_VALUE;
		smallestPayoff = Double.MAX_VALUE;
		biggestPayoff = -Double.MAX_VALUE;
		observedActionsToInformationSetId[1] = new HashMap<List<String>, Integer>();
		observedActionsToInformationSetId[2] = new HashMap<List<String>, Integer>();
		systemProbability[0] = new HashMap<String,Double>();
		systemProbability[1] = new HashMap<String,Double>();
	}
	
	public Game(String filename) {
		this();
		//createGameFromFile(filename);
	}
	
	public void applySignalAbstraction(SignalAbstraction signalAbstraction) {
		for (int nodeId = 0; nodeId < getNumNodes(); nodeId++) {
			Node node = getNodeById(nodeId);
			if (node.getPlayer() == 1 || node.getPlayer() == 2) {
				// Get observed nature actions, then concatenate observed player actions
				List<String> observedActions = extractObservedNatureActionsFromNodeName(node.getName(), node.getPlayer());
				observedActions.addAll(extractObservedPlayerActionsFromNodeName(node.getName(), node.getPlayer()));
				// Uniquely identify each information set by the (out of order) list of observed actions. This works for signal-decomposable games.
				observedActionsToInformationSetId[node.getPlayer()].put(observedActions, node.getInformationSet());
			}
		}
		this.signalAbstraction = signalAbstraction;
		abstraction = new int[3][];
		abstraction[1] = new int[getNumInformationSetsPlayer1()];
		abstraction[2]= new int[getNumInformationSetsPlayer2()];
		applySignalAbstractionRecursive(getRoot(), new ArrayList<Integer>());
		hasAbstraction = true;
		useIdentityActionMap = true;
	}
	
	private void applySignalAbstractionRecursive(int currentNodeId, List<Integer> natureIndices) {
		Node node = getNodeById(currentNodeId);
		if (node.isLeaf()) {
			return;
		}
		
		if (node.getPlayer() == 1 || node.getPlayer() ==2) {
			List<String> natureSignals = extractObservedNatureActionsFromNodeName(node.getName(), node.getPlayer());
			List<String> abstractNatureSignals = signalAbstraction.getAbstractSignalsByName(natureSignals);
			List<String> observedPlayerActions = extractObservedPlayerActionsFromNodeName(node.getName(), node.getPlayer());
			// Make abstract observed list
			List<String> abstractActions = new ArrayList<String>(abstractNatureSignals);
			abstractActions.addAll(observedPlayerActions);
			int abstractInformationSetId = observedActionsToInformationSetId[node.getPlayer()].get(abstractActions);
			node.setAbstractInformationSet(abstractInformationSetId);
			if (node.getInformationSet() != abstractInformationSetId) {
				int t = 1;
			}
			abstraction[node.getPlayer()][node.getInformationSet()] = abstractInformationSetId;
		}
		for (Action action : node.getActions()) {
			if (node.getPlayer() == 0) {
				natureIndices.add(depth);
				applySignalAbstractionRecursive(action.getChildId(), natureIndices);
				natureIndices.remove(natureIndices.size()-1);
			} else {
				applySignalAbstractionRecursive(action.getChildId(), natureIndices);
			}			
		}
	}
	
	public void createGameFromFileZerosumPackageFormat(String filename) {
		//BufferedReader in = null;
		CSVReader in = null;
		try {
			in= new CSVReader(new FileReader(filename), ' ', '\'');
			//in = new BufferedReader(new FileReader(filename));
		} catch (FileNotFoundException e) {
			System.out.println("Game::CreateGameFromFile: File not found");
			System.out.println("filename: " + filename);
			System.exit(0);
		}
		
		String[] splitLine;
		try {
			while ((splitLine = in.readNext()) != null) {
				// splitLine may contain empty strings. We filter these out here. This should preferably be handled by a library function. 
				List<String> filtered = new ArrayList<String>();
				for(String s : splitLine) {
					if(!s.equals("")) {
						filtered.add(s);
					}
				}
			splitLine = filtered.toArray(new String[0]);

				if (splitLine.length == 0) {
					continue;
				} else if (splitLine[0].equals("EFG")) {
					readGameInfoLine(splitLine);
					continue;
				} /*else if (!StringUtils.isNumeric(splitLine[0])) {
					readGameInfoLine(splitLine);
				} */else {
					if (splitLine[0].equals("t")) {
						CreateLeafNode(splitLine);
						//System.out.println("T");
					} else if (splitLine[0].equals("c")) {
						CreateZeroSumPackageStyleNatureNode(splitLine);
					
					} else {
						CreatePlayerNode(splitLine);
						//System.out.println("p");
					}
				}
			}
		} catch (IOException e) {
			System.out.println("Game::CreateGameFromFile: Read exception");
		}
		
	}
	
	
	
	private void readGameInfoLine(String [] split_line) {
		numNodes = Utils.TOTAL_NUMBER_OF_NODE;
		numInformationSetsPlayer1 = Utils.NUM_INFO_SET_PLAYER_1;
		numInformationSetsPlayer2 = Utils.NUM_INFO_SET_PLAYER_2;
		
		informationSets[0] = new TIntArrayList [numInformationSetsPlayer1];
		informationSets[1] = new TIntArrayList [numInformationSetsPlayer2];
		
		informationSetsSeen[0] = new boolean[numInformationSetsPlayer1];
		informationSetsSeen[1] = new boolean[numInformationSetsPlayer2];
		
		for (int i = 0; i < numInformationSetsPlayer1; i++) {
			informationSets[0][i] = new TIntArrayList();
		}
		for (int i = 0; i < numInformationSetsPlayer2; i++) {
			informationSets[1][i] = new TIntArrayList();
		}
		
		nodes = new Node[numNodes];
		childNodeIdBySignalId = new TIntIntMap [numNodes];
		actionIdBySignalId = new TIntIntMap [numNodes];
		for (int i = 0; i < numNodes; i++) {
			childNodeIdBySignalId[i] = new TIntIntHashMap();
			actionIdBySignalId[i] = new TIntIntHashMap();
		}
	}
	
	// CreateLeafNode handles both Zerosum format files, and the more heavily annotated files of this package
	private void CreateLeafNode(String[] line) {
		Node node = new Node();
		String line1 = line[1].replace("\"", "");
		node.nodeId = Integer.parseInt(line1);
		node.name = line[0];
		node.player = -2;
		node.valuePlayerOne = Double.parseDouble(line[6]);
		node.valuePlayerTwo = Double.parseDouble(line[7]);
		
		/*
		if (node.value < smallestPayoff) {
			smallestPayoff = node.value;
		}
		if (node.value > biggestPayoff) {
			biggestPayoff = node.value;
		}*/
		//System.out.println("Node val:" + node.value);
		nodes[node.nodeId] = node;
	}

	// The format is the same for player nodes in the Zerosum package and our format 
	private void CreatePlayerNode(String[] line) {
		Node node = new Node();
		String line1 = line[1].replace("\"", "");
		node.nodeId = Integer.parseInt(line1);
		node.player = Integer.parseInt(line[2]);
		node.informationSet = Integer.parseInt(line[3]);
		if(node.player == 1)
			parentInfoSet = node.informationSet;
		//System.out.println("Player: " + (node.player-1) + ", info set: " + node.informationSet);
		if (node.informationSet < smallestInformationSetId[node.player-1]) {
			smallestInformationSetId[node.player-1] = node.informationSet;
		}
		
		node.name = line[0];
		//System.out.println("Player: " + (node.player-1) + ", info set: " + node.informationSet);
		//informationSets[node.player-1][node.informationSet].add(node.nodeId);
		
		int numActions = line.length-8;
		node.actions = new Action[numActions];
		for (int i = 0; i < numActions; i++) {
			/*if (!informationSetsSeen[node.player-1][node.informationSet]) {
				numSequences[node.player-1]++;
			}else {
				System.out.println("Information already seen");
			}*/
			numSequences[node.player-1]++;
			Action action = new Action();
			action.name = line[6+i].replace("\"", "");
			//System.out.println("action name = " + action.name + "info :" + node.informationSet);
			if(node.player == 1) {
				action.childId = node.nodeId + (i*(Utils.MAX_NO_ATTACKER_ACTIONS+1)) + 1;
				//System.out.println("node id : " + node.nodeId + "  child id:" + action.childId);
			}
			else {
				action.childId = node.nodeId + i + 1;
				//System.out.println("action name = " + action.name + "child id:" + action.childId);
			}
			node.actions[i] = action;
		}
			//System.out.println("Info : " + node.informationSet + "node Id: " + node.nodeId);
			informationSets[node.player - 1][node.informationSet].add(node.nodeId);
			informationSetsSeen[node.player - 1][node.informationSet] = true;

		nodes[node.nodeId] = node;
	}
	
	
	/**
	 * Assumes that the name of a node is the string of actions performed to reach the node. Returns the subset of actions that are observed by player i.
	 * Assumes that actions are split by '/' and values are written [01a];actionName, where [01a] indicates whether the observer is 0,1, or a
	 * @param node
	 * @param player observing player
	 * @return
	 */
	public static List<String> extractObservedActionsFromNodeName(String name, int player) {
		List<String> observed = new ArrayList<String>();
		String[] actions = name.split("/");
		// start at 1, since the first action is the empty action at the root
		for (int i = 1; i < actions.length; i++) {
			String[] splitAction = actions[i].split(";");
			if (splitAction[1].equals("a") || Integer.parseInt(splitAction[1]) == player-1) {
				observed.add(splitAction[2]);
			}
		}
		
		return observed;
	}
	
	/**
	 * Assumes that the name of a node is the string of actions performed to reach the node. Returns the subset of actions that are observed by player i.
	 * Assumes that actions are split by '/' and values are written [01a];actionName, where [01a] indicates whether the observer is 0,1, or a
	 * @param node
	 * @param player observing player
	 * @return
	 */
	public static List<String> extractObservedNatureActionsFromNodeName(String name, int player) {
		List<String> observed = new ArrayList<String>();
		String[] actions = name.split("/");
		// start at 1, since the first action is the empty action at the root
		for (int i = 1; i < actions.length; i++) {
			String[] splitAction = actions[i].split(";");
			if (splitAction[0].equals("n") && (splitAction[1].equals("a") || Integer.parseInt(splitAction[1]) == player-1)) {
				observed.add(splitAction[2]);
			}
		}
		
		return observed;
	}

	/**
	 * Assumes that the name of a node is the string of actions performed to reach the node. Returns the subset of actions that are observed by player i.
	 * Assumes that actions are split by '/' and values are written [01a];actionName, where [01a] indicates whether the observer is 0,1, or a
	 * @param node
	 * @param player observing player
	 * @return
	 */
	public static List<String> extractObservedPlayerActionsFromNodeName(String name, int player) {
		List<String> observed = new ArrayList<String>();
		String[] actions = name.split("/");
		// start at 1, since the first action is the empty action at the root
		for (int i = 1; i < actions.length; i++) {
			String[] splitAction = actions[i].split(";");
			if (!splitAction[0].equals("n") && (splitAction[1].equals("a") || Integer.parseInt(splitAction[1]) == player-1)) {
				observed.add(splitAction[2]);
			}
		}
		
		return observed;
	}

	private void insertFeatureProbability(String action, double probability) {

		String realFeature, hpFeature;
/*		if (action.substring(0, 1).equals("1")) {

			realFeature = action.substring(1, Utils.REAL_HOST_FEATURES_NUM + 1);
			hpFeature = action.substring(Utils.REAL_HOST_FEATURES_NUM + 2);
		} else*/ {
			realFeature = action.substring(0, Utils.REAL_HOST_FEATURES_NUM);
			hpFeature = action.substring(Utils.REAL_HOST_FEATURES_NUM);
			//System.out.println(realFeature + " : " + hpFeature);
		}
		
		if(systemProbability[0].containsKey(realFeature)){
			
			systemProbability[0].put(realFeature, systemProbability[0].get(realFeature) + probability);
		}else {
			systemProbability[0].put(realFeature,probability);
		}
		
		if(systemProbability[1].containsKey(hpFeature)){
			systemProbability[1].put(hpFeature, systemProbability[1].get(hpFeature) + probability);
		}else {
			systemProbability[1].put(hpFeature,probability);
		}
		
		//System.out.println(realFeature+  "real"+ systemProbability[0].get(realFeature));
	}
	
	private void CreateZeroSumPackageStyleNatureNode(String[] line) {
		
		
		Node node = new Node();
		String line1 = line[1].replace("\"", "");
		node.nodeId = Integer.parseInt(line1);
		//System.out.println("Node" + node.nodeId);
		node.name = line[0];
		node.player = 0;
		int numActions = (line.length - 7)/2;
		node.actions = new Action[numActions];
		nodes = new Node[numNodes]; // TODO programaticlly need to handle
		double sum = 0;
		for (int i = 0; i < numActions; i++) {
			Action action = new Action();
			action.name = line[((3+i)*2)-1].replace("\"", "");
			action.childId = i*(((Utils.MAX_NO_ATTACKER_ACTIONS+1)*Utils.numOfDefenderActions)+1) + 1;
			//System.out.println(action.name + " child id : " + action.childId);
			action.probability = Double.parseDouble(line[(3+i)*2]);
			sum += action.probability;
			node.actions[i] = action;		
			//System.out.println("Prob :" + action.probability);
			insertFeatureProbability(action.name, action.probability);
		}
		

		/*
		for (int i = 0; i < numActions; i++) {
			node.actions[i].probability = (double) node.actions[i].probability / sum;
			//System.out.println("Normalize prob :" + node.actions[i].probability);
		}*/
		// the root node is the empty history
	
		root = node.nodeId;
		nodes[node.nodeId] = node;
	}


	/**
	 * Computes an array that represents the expected value for each node
	 * @param strategyP1
	 * @param strategyP2
	 * @param invertValues if true, all values are negated, representing the utility for Player 2 when considered as a maximizing player
	 * @return
	 */
	public double[] getExpectedValuesForNodes(TObjectDoubleMap<String>[] strategyP1, TObjectDoubleMap<String>[] strategyP2, boolean negateValues) {
		/*double[] expectedValue = new double[numNodes];
		fillExpectedValueArrayRecursive(expectedValue, root, strategyP1, strategyP2, negateValues, ZeroBranchOption.ZERO, false);
		return expectedValue;*/
		return getExpectedValuesForNodes(strategyP1, strategyP2, negateValues, null);
	}
	
	/**
	 * Computes an array that represents the expected value for each node
	 * @param strategyP1
	 * @param strategyP2
	 * @return
	 */
	public double[] getExpectedValuesForNodes(TObjectDoubleMap<String>[] strategyP1, TObjectDoubleMap<String>[] strategyP2) {
		return getExpectedValuesForNodes(strategyP1, strategyP2, false);
	}

		/**
	 * Computes an array that represents the expected value for each node
	 * @param strategyP1
	 * @param strategyP2
	 * @return
	 */
	public double[] getExpectedValuesForNodes(TObjectDoubleMap<String>[] strategyP1, TObjectDoubleMap<String>[] strategyP2, boolean negateValues, NormalDistribution distribution) {
		double[] expectedValue = new double[numNodes];
		fillExpectedValueArrayRecursive(expectedValue, root, strategyP1, strategyP2, negateValues, ZeroBranchOption.ZERO, false, distribution);
		return expectedValue;
	}

	// Enum specifies how to handle the expected value of branches with probability zero of being reached.
	// ZERO: This option places expected value of zero on all nodes in a probability 0 subtree
	// UNIFORM: This option uses uniform probabilities
	private enum ZeroBranchOption {ZERO, UNIFORM} // TODO: implement UNIFORM option

	private double fillExpectedValueArrayRecursive(double[] array, int currentNode, TObjectDoubleMap<String>[] strategyP1, TObjectDoubleMap<String>[] strategyP2, boolean negateValues, ZeroBranchOption zeroBranchOption, boolean inZeroBranch, NormalDistribution distribution) {
		Node node = nodes[currentNode];
		//biggestPayoff = 0;
		//smallestPayoff = 0;
		if (node.isLeaf()) {
			if (inZeroBranch) {
				//array[currentNode] = 0;
				array[currentNode] = negateValues ? -node.getValue() + biggestPayoff: node.getValue() - smallestPayoff;
			}
			else {
				array[currentNode] = negateValues ? -node.getValue() + biggestPayoff: node.getValue() - smallestPayoff;
			}
			return array[currentNode];
		}

		
		array[currentNode] = 0;
		for(Action action : node.actions) {
			double probability = 0;
			if (node.getPlayer() == 0) {
				probability = action.getProbability();
			} else if (node.getPlayer() == 1){
				probability = strategyP1[node.getInformationSet()].get(action.getName());
			} else {
				probability = strategyP2[node.getInformationSet()].get(action.getName());
			}
			
			if (null == distribution) {
				probability = inZeroBranch ? 0 : probability;
				array[currentNode] += probability * (fillExpectedValueArrayRecursive(array, action.childId, strategyP1, strategyP2, negateValues, zeroBranchOption, probability == 0, distribution));
			} else {
				array[currentNode] += probability * fillExpectedValueArrayRecursive(array, action.childId, strategyP1, strategyP2, negateValues, zeroBranchOption, probability == 0, distribution) + distribution.sample();
			}
		}
		return array[currentNode];
	}
	
	
	public TIntArrayList getInformationSet(int player, int informationSetId) {
		if (hasAbstraction) {
			System.out.println("Warning: abstraction exists, getInformationSet not updated to reflect this");
		}
		return informationSets[player-1][informationSetId];
	}

	public int getNumActionsAtInformationSet(int player, int informationSetId) {
		if(informationSets[player-1][informationSetId].size() > 0)
			return nodes[informationSets[player-1][informationSetId].get(0)].getActions().length;
		return 0;
		
	}

	public Action[] getActionsAtInformationSet(int player, int informationSetId) {
		return nodes[informationSets[player-1][informationSetId].get(0)].getActions();
	}
	
	public int getNumActionsForNature(GameState gs) {
		return nodes[gs.getCurrentNodeId()].getActions().length;
	}

	
	public boolean[][] getInformationSetsSeen() {
		return informationSetsSeen;
	}

	public Node[] getNodes() {
		return nodes;
	}

	public TIntIntMap[] getChildNodeIdBySignalId() {
		return childNodeIdBySignalId;
	}

	public TIntIntMap[] getActionIdBySignalId() {
		return actionIdBySignalId;
	}

	public int getRoot() {
		return root;
	}

	public int getNumChanceHistories() {
		return numChanceHistories;
	}

	public int getNumCombinedPlayerHistories() {
		return numCombinedPlayerHistories;
	}

	public int getNumTerminalHistories() {
		return numTerminalHistories;
	}

	public int getNumNodes() {
		return numNodes;
	}

	public int getNumInformationSetsPlayer1() {
		return numInformationSetsPlayer1;
	}

	public int getNumInformationSetsPlayer2() {
		return numInformationSetsPlayer2;
	}

	public int[] getNumSequences() {
		return numSequences;
	}
	
	public int getNumSequencesP1() {
		return numSequences[0];
	}

	public int getNumSequencesP2() {
		return numSequences[1];
	}

	public String[] getSignals() {
		return signals;
	}

	public TObjectIntMap<String> getSignalNameToId() {
		return signalNameToId;
	}

	public int getNumRounds() {
		return numRounds;
	}

	public int getDepth() {
		return depth;
	}

	public int getNumPrivateSignals() {
		return numPrivateSignals;
	}

	public Node getNodeById(int currentNodeId) {
		return nodes[currentNodeId];
	}

	public int getSmallestInformationSetIdPlayer1() {
		return smallestInformationSetId[0];
	}

	public int getSmallestInformationSetIdPlayer2() {
		return smallestInformationSetId[1];
	}
	
	public int getSmallestInformationSetId(int player) {
		return smallestInformationSetId[player-1];
	}
	public double getSystemProbability(int type,String action) {
		return systemProbability[type].get(action);
	}

	public void setSystemProbability(int type,String action, double probability) {
		systemProbability[type].put(action,probability);
	}

	@Override
	public GameState getInitialGameState() {
		GameState gs = new GameState();
//		gs.setCurrentNodeId(getRoot());
//		gs.setCurrentPlayer(nodes[getRoot()].getPlayer());
//		if (hasAbstraction) {
//			gs.setCurrentInformationSetId(abstraction[nodes[getRoot()].getInformationSet()]);
//		} else {
//			gs.setCurrentInformationSetId(nodes[getRoot()].getInformationSet());
//		}
		gs.nodeIdHistory.add(getRoot());
		updateGameStateInfo(gs);
		return gs;
	}

	public int getNumActions(GameState gs) {
		if (gs.getCurrentPlayer() == 0) {
			return getNumActionsForNature(gs);
		} else {
			return getNumActionsAtInformationSet(gs.getCurrentPlayer(), gs.getCurrentInformationSetId());
		}
	}

	public int getNumActionsAtInformationSet(GameState gs) {
		return getNumActionsAtInformationSet(gs.getCurrentPlayer(), gs.getCurrentInformationSetId());
	}

	@Override
	public void updateGameStateWithAction(GameState gs, int actionId, double probability) {
		gs.addHistory(gs.getCurrentPlayer(), actionId);
		gs.addProbability(gs.getCurrentPlayer(), probability);
		int childNodeId = nodes[gs.nodeIdHistory.get(gs.nodeIdHistory.size()-1)].actions[actionId].getChildId();
		gs.nodeIdHistory.add(childNodeId);
		updateGameStateInfo(gs);
	}

	@Override
	public void removeActionFromGameState(GameState gs, int action, int player) {
		gs.popAction(player);
		gs.popProbability(player);
		gs.nodeIdHistory.remove(gs.nodeIdHistory.size()-1, 1);
		updateGameStateInfo(gs);
	}

	private void updateGameStateInfo(GameState gs) {
		Node newNode = nodes[gs.getCurrentNodeId()];
		
		//gs.nodeIdHistory.add(newNode.getNodeId());
		if (!newNode.isLeaf() && hasAbstraction && newNode.player != 0 && abstraction[newNode.getPlayer()][newNode.getInformationSet()] != newNode.getInformationSet()) {
			gs.setCurrentInformationSetId(abstraction[newNode.getPlayer()][newNode.getInformationSet()]);
			gs.setOriginalInformationSetId(newNode.getInformationSet());
		} else if (!newNode.isLeaf() && newNode.player != 0){
			gs.setCurrentInformationSetId(newNode.getInformationSet());
			gs.setOriginalInformationSetId(newNode.getInformationSet());
		}
		//gs.setCurrentInformationSetId(newNode.getInformationSet());
		
		gs.setCurrentPlayer(newNode.getPlayer());
		
		if (newNode.isLeaf()) {
			gs.setIsLeaf(true);
			gs.setValueP1(newNode.getPlayerOneValue());
			gs.setValueP2(newNode.getPlayerTwoValue());
		} else {
			gs.setIsLeaf(false);
		}
	}
	
	public double getProbabilityOfNatureAction(GameState gs, int action) throws Exception {
		if (gs.getCurrentPlayer() != 0) {
			throw new Exception("Not a nature state");
		}
		return this.nodes[gs.getCurrentNodeId()].actions[action].getProbability();
	}

	@Override
	public int getNumInformationSets(int player) {
		if (player == 1) {
			return numInformationSetsPlayer1;
		} else if (player == 2) {
			return numInformationSetsPlayer2;
		}
		return 0;
	}
	@Override
	public boolean informationSetAbstracted(int player, int informationSetId) {
		if (hasAbstraction) {
			return informationSetId != abstraction[player][informationSetId];
		} else {
			return false;
		}
	}

	@Override
	public int getAbstractInformationSetId(int player, int informationSetId) {
		if (hasAbstraction) {
			return abstraction[player][informationSetId];
		} else {
			return informationSetId;
		}
	}

	@Override
	public void addInformationSetAbstraction(int[][] informationSetAbstraction,	int[][][] actionMapping) {
		this.hasAbstraction = true;
		this.useIdentityActionMap = false;
		this.abstraction = informationSetAbstraction;
		this.actionAbstractionMapping = actionMapping;
	}

	@Override
	public int getAbstractActionMapping(int player, int originalInformationSetId, int originalAction) {
		if (informationSetAbstracted(player, originalInformationSetId) && !useIdentityActionMap) {
			return actionAbstractionMapping[player][originalInformationSetId][originalAction];
		} else {
			return originalAction;
		}
	}
	
	@Override
	public int getAbstractActionMapping(GameState gs, int action) {
		if (informationSetAbstracted(gs.getCurrentPlayer(), gs.getOriginalInformationSetId()) && !useIdentityActionMap) {
			return actionAbstractionMapping[gs.getCurrentPlayer()][gs.getOriginalInformationSetId()][action];
		} else {
			return action;
		}
	}



	@Override
	public double computeGameValueForStrategies(double[][][] strategyProfile) {
		return computeGameValueRecursive(getRoot(), strategyProfile);
	}

	private double computeGameValueRecursive(int currentNodeId, double[][][] strategyProfile) {
		Node currentNode = getNodeById(currentNodeId);
		if (currentNode.isLeaf()) {
			return currentNode.getValue();
		}
		
		double value = 0;
		for (int actionId = 0; actionId < currentNode.getActions().length; actionId++) {
			Action action = currentNode.actions[actionId];
			double probability = currentNode.player == 0 ? action.getProbability() : strategyProfile[currentNode.getPlayer()][currentNode.getInformationSet()][actionId];
			value += probability * computeGameValueRecursive(action.getChildId(), strategyProfile);
		}
		
		return value;
	}

	@Override
	public double getLargestPayoff() {
		return biggestPayoff;
	}
	
	@Override
	public String toString(){
		return recursiveToString(getRoot(), "");
	}
	
	private String recursiveToString(int nodeId, String prefix) {
		Node node = getNodeById(nodeId);
		String stringRep = prefix + node.getName();
		if (node.isLeaf()) return stringRep;
		for (Action action : node.getActions()) {
			stringRep += " " + action;
		}
		stringRep += "\n";
		for (Action action : node.getActions()) {
			stringRep += recursiveToString(action.getChildId(), prefix+" ");
		}
		return stringRep;
	}
}