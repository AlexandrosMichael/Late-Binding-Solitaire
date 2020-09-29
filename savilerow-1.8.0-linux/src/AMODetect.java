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
import java.math.BigInteger;
import java.io.*;

//  Store mutexes discovered by Minion between pairs of literals, and 
//  collect mutexes into AMO relations. 

public class AMODetect {
    ////////////////////////////////////////////////////////////////////////////
    //
    //   AMO adjacency list read from Minion during domain filtering.
    
    // Maps a number to a bool variable name. Used to give a unique number to each bool variable.
    // First entry should be null.
    public static ArrayList<String> varslist;
    public static HashMap<String, Integer> vartonum;  // Inverse mapping of above. 
    //  Adjlist maps from ints to ints.  Negative int means negated bool var. 
    public static HashMap<Integer, HashSet<Integer>> adjlist;
    
    public static void init() {
        //  Representation of adjacency list -- map between variables and integers
        varslist=new ArrayList<String>();  // Maps a number to a variable. Used to give a unique number to each variable.
        varslist.add(null);  // Can't use number 0. 
        
        vartonum=new HashMap<String, Integer>();
        //  Adjlist maps from ints to ints.
        adjlist=new HashMap<Integer, HashSet<Integer>>();
    }
    
    public static int add_variable_amo(String var) {
        if(!vartonum.containsKey(var)) {
            int number=varslist.size();
            vartonum.put(var, number);
            varslist.add(var);
            adjlist.put(number, new HashSet<Integer>());    // Extend the adjacency list.
            adjlist.put(-number, new HashSet<Integer>());   
            return number;
        }
        else {
            return vartonum.get(var);
        }
    }
    
    public static void addEdge(int idx1, int idx2) {
        adjlist.get(idx1).add(idx2);
        adjlist.get(idx2).add(idx1);
    }
    
    public static ArrayList<TreeSet<Integer>> buildCliques(TreeSet<String> loose_bools, HashMap<String, ASTNode> loose_coeffs) {
        for(String bool : loose_bools) {
            //  Make sure graph ds initialised for every variable in this ct. 
            AMODetect.add_variable_amo(bool);
        }
        
        //   Sort by degree within the sub-graph.
        //  Pair class used for sorting 
        class IdxDegreePair implements Comparable<IdxDegreePair> {
            public int idx;
            public int degree;
            public IdxDegreePair(int _idx, int _degree) {
                idx=_idx;
                degree=_degree;
            }
            public int compareTo(IdxDegreePair o) {
                if(degree<o.degree) {
                    return 1;
                }
                else if(degree==o.degree) {
                    return 0;
                }
                else {
                    return -1;
                }
            }
            public String toString() {
                return "("+idx+", "+degree+")";
            }
        }
        
        TreeSet<Integer> loose_bools_idx_set=new TreeSet<Integer>();  //  Set of available indices, opposite polarity ones get removed from here.
        
        ArrayList<IdxDegreePair> loose_bools_idx=new ArrayList<IdxDegreePair>(); //  List of all indices -- not just available ones.
        
        
        for(String varname : loose_bools) {
            int idx=vartonum.get(varname);
            
            loose_bools_idx_set.add(idx);
            loose_bools_idx_set.add(-idx);
        }
        
        // Populate loose_bools_idx then sort by degree.
        for(String varname : loose_bools) {
            int idx=vartonum.get(varname);
            // Degree of positive literal
            int degpos=0;
            for(Integer i : adjlist.get(idx)) {
                if(loose_bools_idx_set.contains(i)) {
                    degpos++;
                }
            }
            
            loose_bools_idx.add(new IdxDegreePair(idx, degpos));
            
            // Degree of negative literal
            int degneg=0;
            for(Integer i : adjlist.get(-idx)) {
                if(loose_bools_idx_set.contains(i)) {
                    degneg++;
                }
            }
            
            loose_bools_idx.add(new IdxDegreePair(-idx, degneg));
        }
        
        Collections.sort(loose_bools_idx);
        
        //  Iterate through loose_bools_idx adding to cliques. 
        //  Version 1: adds first suitably connected vertex from the list.
        /*for(int i=0; i<loose_bools_idx.size(); i++) {
            int v=loose_bools_idx.get(i).idx;
            
            if(loose_bools_idx_set.contains(v)) {
                //  Construct one clique.
                TreeSet<Integer> clique=new TreeSet<Integer>();
                
                loose_bools_idx_set.remove(v);
                loose_bools_idx_set.remove(-v);
                
                clique.add(v);
                
                for(int j=i+1; j<loose_bools_idx.size(); j++) {
                    int proposeVertex=loose_bools_idx.get(j).idx;
                    
                    if(loose_bools_idx_set.contains(proposeVertex)) {
                        boolean connected=true;
                        
                        for(Integer cliqueVertex : clique) {
                            if(!AMODetect.adjlist.get(cliqueVertex).contains(proposeVertex)) {
                                connected=false;
                                break;
                            }
                        }
                        
                        if(connected) {
                            clique.add(proposeVertex);
                            loose_bools_idx_set.remove(proposeVertex);
                            loose_bools_idx_set.remove(-proposeVertex);
                        }
                    }
                }
                
                cliques.add(clique);
            }
        }*/
        
        //  Iterate through loose_bools_idx adding to cliques. 
        //  Version 2: makes a list of all connected vertices, then adds a max degree one that has most
        //  popular coeff in clique.
        ArrayList<TreeSet<Integer>> cliques=new ArrayList<TreeSet<Integer>>();
        
        long candidatesDegree=-1;
        ArrayList<Integer> candidates=new ArrayList<Integer>();
        
        for(int i=0; i<loose_bools_idx.size(); i++) {
            int v=loose_bools_idx.get(i).idx;
            
            if(loose_bools_idx_set.contains(v)) {
                //  Construct one clique.
                TreeSet<Integer> clique=new TreeSet<Integer>();
                
                loose_bools_idx_set.remove(v);
                loose_bools_idx_set.remove(-v);
                
                clique.add(v);
                
                while(true) {
                    
                    //  Make a list of max-degree candidates for inclusion in the clique.
                    candidatesDegree=-1;
                    candidates.clear();
                    
                    loose_bools_idx_loop:
                    for(int j=i+1; j<loose_bools_idx.size(); j++) {
                        int proposeVertex=loose_bools_idx.get(j).idx;
                        long proposeVertexDeg=loose_bools_idx.get(j).degree;
                        
                        if(candidatesDegree!=-1 && proposeVertexDeg<candidatesDegree) {
                            break loose_bools_idx_loop;  //  Gone past ones with same degree as other candidates.
                        }
                        
                        if(loose_bools_idx_set.contains(proposeVertex)) {
                            boolean connected=true;
                            
                            for(Integer cliqueVertex : clique) {
                                if(!adjlist.get(cliqueVertex).contains(proposeVertex)) {
                                    connected=false;
                                    break;
                                }
                            }
                            
                            if(connected) {
                                assert candidatesDegree==-1 || candidatesDegree==proposeVertexDeg;
                                candidatesDegree=proposeVertexDeg;
                                candidates.add(proposeVertex);
                            }
                        }
                    }
                    
                    if(candidates.size()==0) {
                        break;
                    }
                    
                    // Now we have all candidates of the highest possible degree.
                    // Choose one whose coeff is equal (absolute value) to the most others in the clique.
                    int proposeVertex=-1;
                    int coeffsCommon=-1;
                    
                    for(int j=0; j<candidates.size(); j++) {
                        int idx=candidates.get(j);
                        
                        String nam=varslist.get((idx<0)?-idx:idx);
                        long coeff=loose_coeffs.get(nam).getValue();
                        int coeffsCommonWithThis=0;
                        // Count how many from clique it is equal to.
                        for(int k : clique) {
                            String nam2=varslist.get((k<0)?-k:k);
                            if(loose_coeffs.get(nam2).getValue()==coeff) {
                                coeffsCommonWithThis++;
                            }
                        }
                        
                        if(coeffsCommonWithThis>coeffsCommon) {
                            coeffsCommon=coeffsCommonWithThis;
                            proposeVertex=idx;
                        }
                    }
                    
                    clique.add(proposeVertex);
                    loose_bools_idx_set.remove(proposeVertex);
                    loose_bools_idx_set.remove(-proposeVertex);
                }
                
                cliques.add(clique);
            }
        }
        
        return cliques;
    }
    
    
}