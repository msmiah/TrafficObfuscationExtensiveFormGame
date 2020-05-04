package ExperimentMain;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.text.NumberFormat;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import au.com.bytecode.opencsv.CSVReader;
import extensive_form_efg_game_format.CreateTree;
import extensive_form_game.Game;
import extensive_form_game_solver.DefenderSequenceFormLPApproximationSolver;
import ilog.concert.IloException;
import utils.Utils;



/**
 * @author IASRLUserv     
 *
 */
public class TestMain {

	public static void main(String[] args) throws IOException {
		
		int numOfSimulation = 100;
		int possibleCombination = (int) Math.pow(2.0, (double) Utils.REAL_HOST_FEATURES_NUM);
	//	writeFeatureDistribution(possibleCombination,numOfSimulation);
		double[][][] distributions = readDistributions("featuredristibution.txt",numOfSimulation,possibleCombination);
		CreateTree gameTree = new CreateTree("games/hsg_game", true, distributions[0][0],
				distributions[0][1]);
		gameTree.init();
		gameTree.closeFile();
		Game experimentGame = new Game();
		experimentGame.createGameFromFileZerosumPackageFormat("games/hsg_game.efg"); 
		
		DefenderSequenceFormLPApproximationSolver equilibriumSolver = new DefenderSequenceFormLPApproximationSolver(
				experimentGame, 1);
		equilibriumSolver.solveGame();
		equilibriumSolver.getStrategyProfile();
		try {
			equilibriumSolver.writeStrategyToFile("strategy.txt");
		} catch (IloException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		//double gameValue = equilibriumSolver.getGameValue();
		
			
	}
	
	public static double[][][] readDistributions(String filename, int numSimulation, int numCombination) {
		double[][][] featureDistributions = new double[numSimulation][2][numCombination];
		CSVReader in = null;
		int simIndex = 0;
		try {
			in = new CSVReader(new FileReader(filename), ',');
			// in = new BufferedReader(new FileReader(filename));
		} catch (FileNotFoundException e) {
			System.out.println("File not found");
			System.out.println("filename: " + filename);
			System.exit(0);
		}

		String[] splitLine;
		try {
			while ((splitLine = in.readNext()) != null) {
				int indexCnt = 0;
				for (String s : splitLine) {
					if (!s.equals("")) {
						try {
							NumberFormat nf = NumberFormat.getInstance();
							double d = nf.parse(s).doubleValue();
							if (indexCnt < numCombination)
								featureDistributions[simIndex][0][indexCnt % numCombination] = d;
							else
								featureDistributions[simIndex][1][indexCnt % numCombination] = d;
							++indexCnt;
					  }catch(ParseException ex){
				        }
					
					}
				}
				simIndex++;
			}
		} catch (IOException e) {
			System.out.println("Game::CreateGameFromFile: Read exception");
		}
		return featureDistributions;
	}

	public static void writeFeatureDistribution(int numFeature, int totSimulation) throws IOException {
		FileWriter fw = new FileWriter("featuredristibution.txt");
		for (int i = 0; i < totSimulation; i++) {
			double[] probReal = generateRandomProbability(numFeature);
			double[] probHp = generateRandomProbability(numFeature);
			String probString = "";
			for (int j = 0; j < numFeature; j++) {
				probReal[j] = (Math.round(probReal[j] * 100.0)) / 100.0;
				probString = probString + probReal[j] + ",";
			}
			for (int j = 0; j < numFeature; j++) {
				probHp[j] = (Math.round(probHp[j] * 100.0)) / 100.0;
				probString = probString + probHp[j] + ",";
			}
			fw.write(probString+"\n");
		}
		fw.close();
	}

	
	public static double[] generateRandomProbability(int n) {
		double a[] = new double[n];
		double s = 0.0d;
		Random random = new Random();
		for (int i = 0; i < n; i++) {
			a[i] = 1.0d - random.nextDouble();
			a[i] = -1 * Math.log(a[i]);
			s += a[i];
		}
		for (int i = 0; i < n; i++) {
			a[i] /= s;
		}
		return a;
	}
	
}

/*


import java.util.*;
import java.lang.*;
import java.io.*;

public class Ideone
{
	
private static void permutation(double[] perm, int pos, double[] str) {
    if (pos == perm.length) {
      for(int k = 0; k<perm.length; k++)
          System.out.print(perm[k]+" ");
      System.out.println(" ");
    } else {
        for (int i = 0 ; i < str.length; i++) {
            perm[pos] = str[i];
            permutation(perm, pos+1, str);
        }
    }
}	
	
	
	
	public static void main (String[] args) throws java.lang.Exception
	{
double[] perm = new double[2];
double[] input = {0.1, 0.3, 0.5};
permutation(perm, 0, input);
	}
}*/