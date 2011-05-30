package costabs.handlers;

import java.io.File;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.part.FileEditorInput;

import costabs.console.ConsoleHandler;
import costabs.console.CostabsShellCommand;
import costabs.dialogs.OptionsDialog;
import costabs.structures.ResultTracker;
import costabs.structures.XMLParser;
import costabs.utils.SourceUtils;
import costabs.markers.*;

/**
 * Our sample handler extends AbstractHandler, an IHandler base class.
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class costabsHandler extends AbstractHandler {

	/**
	 * The constructor.
	 */
	public costabsHandler() {
	}

	/**
	 * the command has been executed, so extract the needed information
	 * from the application context.
	 */
	public Object execute(ExecutionEvent event) throws ExecutionException {
		final Shell shellEclipse= HandlerUtil.getActiveWorkbenchWindowChecked(event).getShell();
		
		CostabsShellCommand shell = new CostabsShellCommand();
		
		try {
			ConsoleHandler.defaultConsole = ConsoleHandler.findCostabsConsole();

			String absFile = SourceUtils.extractResource(SourceUtils.obtainActiveEditor()).getLocation().toString();

			// Do costabs directory
			File f = new File("//tmp//costabs//absPL");
			f.mkdirs();
			
			if (CostabsContainer.SELECTED_ITEMS.size() <= 0) {
				Status status = new Status(IStatus.ERROR, "costabs", 0,
			            "No functions or methods selected in the outline view.", null);
				ErrorDialog.openError(shellEclipse, "Costabs Error", "Costabs can not analyze.", status);
				
			}
			else {
				OptionsDialog mDialog = new OptionsDialog (shellEclipse);
				mDialog.open();
				
				if (mDialog.getReturnCode() == OptionsDialog.CANCEL) {
					ConsoleHandler.write("Don't do anything, cancelled by the user");
				} 
				else {
					// If analyze, get preferences and run
					shell.generateProlog(absFile, false);
					shell.analyze(absFile, CostabsContainer.SELECTED_ITEMS.getCalls());
					updateUpperBounds();
					updateMarkers();
				}
				
				// Execute shell commands
				ConsoleHandler.write(shell.getResult());
			}
		}
		catch (Exception e) {
			ConsoleHandler.write(shell.getError());
		}

		return null;
	}
	
	private void updateUpperBounds() {
		
		XMLParser p = new XMLParser("//tmp//costabs//abs.xml");
		ResultTracker r = p.read();
		
		CostabsContainer.STORAGE_UB.mergeUBContent(r);
		CostabsContainer.STORAGE_UB.mergeLineContent(CostabsContainer.SELECTED_ITEMS);
	}
	
	private void updateMarkers() {
		
		// Get the IFile from editor
		IWorkbench iworkbench = PlatformUI.getWorkbench();
		IWorkbenchWindow iworkbenchwindow = iworkbench.getActiveWorkbenchWindow();
		IWorkbenchPage iworkbenchpage = iworkbenchwindow.getActivePage();
		IEditorPart ieditorpart = iworkbenchpage.getActiveEditor();
		IEditorInput input = ieditorpart.getEditorInput();
		IFile file = ((FileEditorInput)input).getFile();
		
		// Clean the actual markers
		UBMarker ub = new UBMarker();
		ub.removeAllMarkers(file);
		
		// Update filling with the actual markers
		CostabsContainer.STORAGE_UB.fillMarkers(file);
		
	}


}