package savilerow;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2020 Peter Nightingale
    
    This file is part of Savile Row.
    
    Savile Row is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.
    
    Savile Row is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.
    
    You should have received a copy of the GNU General Public License
    along with Savile Row.  If not, see <http://www.gnu.org/licenses/>.

*/

import java.util.*;
import java.io.*;

public class MznSolver extends Solver
{
    private Stats stats=null;

    public void findSolutions(String solvername, String filename, Model m) throws IOException,  InterruptedException
    {
        runMznSolver(solvername, filename, m);
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //   Private methods. 
    
    private void runMznSolver(String solvername, String filename, Model m) throws IOException,  InterruptedException
    {
        CmdFlags.runningSolver=true;  // Prevents SR's timeout from kicking in. 
        
        try
        {
            ArrayList<String> command = new ArrayList<String>();
            command.add(solvername);

            if(CmdFlags.getFindAllSolutions()) {
                if(m.objective!=null) {
                    CmdFlags.warning("Ignoring -all-solutions flag because it cannot be used with optimisation.");
                    CmdFlags.setFindAllSolutions(false);
                }
                else {
                    CmdFlags.errorExit("Don't know how to do all solutions with minizinc, sorry.");
                }
            }
            
            if(CmdFlags.getFindNumSolutions()>1) {
                if(m.objective!=null) {
                    CmdFlags.warning("Ignoring -num-solutions flag because it cannot be used with optimisation.");
                    CmdFlags.setFindNumSolutions(1);
                }
                else {
                    CmdFlags.errorExit("Don't know how to do multiple solutions with minizinc, sorry.");
                    // command.add(String.valueOf(CmdFlags.getFindNumSolutions()));
                }
            }
            
            command.add(filename);
            command.addAll(CmdFlags.getSolverExtraFlags());
            
            double srtime=(((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000);
            
            stats = new Stats();
            stats.putValue("SavileRowTotalTime", String.valueOf(srtime));
            stats.putValue("SolverSatisfiable", "1"); // assume it is, will be set to 0 if not
            stats.putValue("SolverTimeOut", "0"); //assume there is no timeout
            
            ArrayList<String> stderr_lines=new ArrayList<String>();
            
            ReadGecodeOutput rgo=new ReadGecodeOutput(this, m.global_symbols);
            
            double solvertime=System.currentTimeMillis();
            
            // System.out.println(command);
            int exitValue=RunCommand.runCommand(true, command, stderr_lines, rgo);
            
            solvertime=(((double) System.currentTimeMillis() - solvertime) / 1000);
            stats.putValue("SolverTotalTime", String.valueOf(solvertime));
           
            if (solvertime > CmdFlags.getTimeLimit()){
                stats.putValue("SolverTimeOut", "1");
            }

            if(stderr_lines.size()!=0 || exitValue!=0) {
                CmdFlags.println("Solver exited with error code:"+exitValue+" and message:");
                CmdFlags.println(stderr_lines);
                CmdFlags.rmTempFiles();
            }
            stats.makeInfoFiles();
        }
        catch(IOException e1) {
            System.err.println("IOException");
            e1.printStackTrace();
            CmdFlags.rmTempFiles();
            throw e1;
        }
        catch(InterruptedException e2) {
            System.err.println("InterruptedException.");
            CmdFlags.rmTempFiles();
            throw e2;
        }
    }
    
    // To be used when parsing all/multiple solutions.
    Solution parseOneSolverSolution(SymbolTable st, BufferedReader in) {
        
        // Grab the text from the current point to the line of 10 minus signs
        try {
            ArrayList<String> solversol=new ArrayList<String>();
            
            String s=in.readLine();
            // System.out.println("LINE: " + s);
            if(s==null) {
                // Reached the end of the stream without seeing ---------- 
                return null;
            }
            if(s.equals("Top level failure!")) {
                // Hack to work around Chuffed
                return null;
            }
            while(!s.equals("----------")) {
                solversol.add(s);
                s=in.readLine();
                // System.out.println("LINE: " + s);
                if(s==null) {
                    return null;
                }
            }
            
            // System.out.println("solversol1 " + solversol);
            Solution sol=solverSolToAST(solversol, st);
            // System.out.println("solversol2 " + sol);
            return sol;
        }
        catch(IOException e) {
            return null;
        }
    }
    
    Solution parseLastSolverSolution(SymbolTable st, BufferedReader in) {
        ArrayList<String> solversol=null;
        while(true) {
            ArrayList<String> solversol1=new ArrayList<String>();
            // Grab the text from the current point to the line of 10 minus signs
            try {
                String s=in.readLine();
                // System.out.println("LINE: " + s);
                if(s==null) {
                    // Reached the end of the stream without seeing ---------- 
                    // get out of the while loop. 
                    break;
                }
                if(s.equals("Top level failure!")) {
                    // Hack to work around Chuffed
                    break;
                }
                
                if(s.equals("=====UNSATISFIABLE=====")) {
                    // No solutions -- just break, and report as UNSAT
                    stats.putValue("SolverSatisfiable", "0");
                    break;
                }

                if(s.equals("=====UNKNOWN====="))
                {
                    stats.putValue("SolverTimeOut", "1");
                    stats.putValue("SolverSatisfiable", "0");
                }

                if(s.equals("==========")) {
                    // No further solution -- just break
                    break;
                }
                
                while(! (s.equals("----------") )) {
                    solversol1.add(s);
                    s=in.readLine();
                    // System.out.println("LINE: " + s);
                    if(s==null) {
                        break;
                    }
                }
                solversol=solversol1;
            }
            catch(IOException e) {
                break;
            }
        }
        
        if(solversol!=null) {
            // System.out.println("solversol1 " + solversol);
            Solution sol=solverSolToAST(solversol, st);
            // System.out.println("solversol2 " + sol);
            return sol;
        }
        else {
            // System.out.println("Returning null");
            return null;
        }
    }
    
    // Takes a solution printed out by a Flatzinc solver
    // and turns it into a hashmap mapping variable name to value.
    HashMap<String, Long> readAllAssignments(ArrayList<String> gecodesol, SymbolTable st) {
        HashMap<String, Long> collect_all_values=new HashMap<String, Long>();
        
        // Each string contains an assignment
        //  var = <num>;
        
        for(int i=0; i<gecodesol.size(); i++) {
            String assign=gecodesol.get(i);
            // System.out.println("assign: " + assign);
            if(!assign.isEmpty()) {   //  Skip empty lines.
                String[] sp=assign.split(";")[0].split(" = ");
                //  Check we have two substrings.
                if(sp.length==2) {
                    // check that this isn't of the form "x = x"
                    if (!sp[0].equals(sp[1])) {
                        String toparse=sp[1].trim();
                        if(toparse.equals("true")) {
                            collect_all_values.put(sp[0], 1L);
                        }
                        else if(toparse.equals("false")) {
                            collect_all_values.put(sp[0], 0L);
                        }
                        else {
                            // System.out.println("toparse " + toparse);
                            collect_all_values.put(sp[0], Long.parseLong(toparse));
                        }
                    }
                }
            }
        }
        
        return collect_all_values;
    }
    
    
    // Thread to read the standard out of gecode and directly parse it, create solution files etc.
    class ReadGecodeOutput extends ReadProcessOutput {
        ReadGecodeOutput(MznSolver _gs, SymbolTable _st) {
            gs=_gs;
            st=_st;
        }
        
        BufferedReader br;
        MznSolver gs;
        SymbolTable st;
        
        public void giveInputStream(BufferedReader _br) {
            br=_br;
        }
        
        public void run() {
            if((!CmdFlags.getFindAllSolutions()) && CmdFlags.getFindNumSolutions()==1) {
                // Find one solution only. Takes the last solution because for optimisation that will be the optimal one. 
                Solution sol = gs.parseLastSolverSolution(st, br);
                if(sol!=null || st.m.incumbentSolution!=null) {
                    gs.createSolutionFile( ((sol!=null)?sol:st.m.incumbentSolution), false);
                }
            }
            else {
                // Multiple solutions. 
                gs.parseAllSolverSolutions(st, br);
            }
        }
    }
}
