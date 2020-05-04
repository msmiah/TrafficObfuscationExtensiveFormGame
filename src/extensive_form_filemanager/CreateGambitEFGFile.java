package extensive_form_filemanager;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;

import extensive_form_efg_game_format.GraphFormat;
import utils.Utils;


public class CreateGambitEFGFile implements GraphFormat {

	private String mFilename;
	private BufferedWriter mBw = null;
	private File mFile;
	private int nodeCount;

	public CreateGambitEFGFile(String filename) {
		mFilename = filename;
		nodeCount = 0;
		init();

	}

	private void init() {

		mFile = new File(mFilename + Utils.FILE_FORMAT);
		FileWriter fw;
		try {
			fw = new FileWriter(mFile);
			mBw = new BufferedWriter(fw);
			if (!mFile.exists()) {
				mFile.createNewFile();
			}

		} catch (IOException e) {
			e.printStackTrace();
		}
		
		String title = "EFG 2 R \"Honeypot Selection game, One-Shot\" { \"Player 1\" \"Player 2 \" }";
		writeToFile(mFilename, title);
	}

	@Override
	public void createChanceNode(String name, int infoset, List actions, List prob, int outcome) {

		String lineEntries = name + " \""+ (nodeCount++) +"\" " + infoset + " \"\"" + " { ";
		for (int i = 0; i < actions.size(); i++) {
			lineEntries += "\"" + actions.get(i) + "\" " + prob.get(i) + " ";
		}
		lineEntries += "} " + outcome;
		writeToFile(mFilename, lineEntries);
		// closeFile();

	}

	@Override
	public void createPlayerNode(String name, int playerNo, int infoset, String infosetName, List actions,
			int outcome) {
		String lineEntries = name +" \""+ (nodeCount++) +"\" " + playerNo + " " + infoset + " \"(" + infosetName + ")\" { ";
		for (int i = 0; i < actions.size(); i++) {
			lineEntries += "\"" + actions.get(i) + "\" ";
		}
		lineEntries += "} " + outcome;
		writeToFile(mFilename, lineEntries);

	}

	@Override
	public void createTerminalNode(String name, int outcome, String outcomeName, List payoffs) {
		String lineEntries = name + " \""+ (nodeCount++) +"\" " + outcome + " \"" + outcomeName + "\" { ";
		for (int i = 0; i < payoffs.size(); i++) {
			lineEntries +=  payoffs.get(i) + " ";
		}
		lineEntries += "} ";
		writeToFile(mFilename, lineEntries);
	}

	private void writeToFile(String filename, String content) {
		try {

			mBw.write(content);
			mBw.newLine();
			//System.out.println("File written Successfully");

		} catch (IOException ioe) {
			ioe.printStackTrace();
		}
	}

	public void closeFile() {
		try {
			if (mBw != null)
				mBw.close();
		} catch (Exception ex) {
			System.out.println("Error in closing the BufferedWriter" + ex);
		}
	}

}
