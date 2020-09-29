package savilerow;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2020 Jordi Coll, Peter Nightingale
    
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

public class Watchdog {
    
    private static long addPolynomialWatchdog(ArrayList<ArrayList<Integer>> Q, ArrayList<ArrayList<Long>> X, int K, boolean useSorter, Sat satModel) throws IOException {
        int n = Q.size();
        
        //This encoding is for < K instead of <= K
        K+=1;
        
        int max = 0;
        for(ArrayList<Integer> q : Q) {
            for(int qi : q) {
                if(qi > max) {
                    max = qi;
                }
            }
        }
        
        int p = floorlog2(max);
        int p2 = exp2(p);
        int m = K / p2;
        if(K%p2 != 0) {
            m++;
        }
        int T = (m*p2) - K;
        
        ArrayList<ArrayList<Long>> B=new ArrayList<>(p+1);  //Buckets
        for(int i=0; i<p+1; i++) {
            B.add(new ArrayList<Long>());
        }
        
        for(int k = 0; k <= p; k++) {
            for(int i = 0; i < n; i++) {
                boolean used = false;
                boolean created = false;
                long vk=0L;  //  Initial value, should never be used.
                for(int j = 0; j < Q.get(i).size(); j++){
                    if(nthBit(Q.get(i).get(j),k)) {
                        if(!used) {
                            vk = X.get(i).get(j);
                            used = true;
                        }
                        else {
                            if(!created) {
                                long aux = satModel.createAuxSATVariable();
                                satModel.addClause(-vk, aux);
                                vk = aux;
                                created=true;
                            }
                            satModel.addClause(-X.get(i).get(j), vk);
                        }
                    }
                }
                if(used) {
                    B.get(k).add(vk);
                }
            }
        }
        
        ArrayList<Long> S = new ArrayList<Long>();
        ArrayList<Long> Shalf = new ArrayList<Long>();
        
        for(int i = 0; i <= p; i++) {
            S.clear();
            ArrayList<Long> U = new ArrayList<>();
            if(useSorter) {
                addSorting(B.get(i), U, true, false, satModel);
            }
            else {
                assert false;
                //addTotalizer(B.get(i), U, satModel);
            }
            if(i==0) {
                // S=U
                copyArrayList(U, S);
            }
            else {
                if(useSorter) {
                    addMerge(U,Shalf,S, true,false, satModel);
                }
                else {
                    addQuadraticMerge(U, Shalf, S, satModel);
                }
            }
            if(nthBit(T,i)) {
                S.add(0, satModel.getTrue());
            }
            
            Shalf.clear();
            for(int j = 1; j < S.size(); j+=2) {
                Shalf.add(S.get(j));
            }
        }
        return S.get(m-1);
    }
    
    public static void addAMOPBGlobalPolynomialWatchdog(ArrayList<ArrayList<Integer>> Q, ArrayList<ArrayList<Long>> X, int K, boolean useSorter, Sat satModel) throws IOException {
        if(K==0) {
            for(ArrayList<Long> v : X) {
                for(Long l : v) {
                    satModel.addClause(-l);
                }
            }
            return;
        }
        else if(K < 0) {
            satModel.addClause(-satModel.getTrue());
            return;
        }
        int n = Q.size();
        
        int maxsum = 0;
        for(int i = 0; i < n; i++) {
            maxsum += Collections.max(Q.get(i));
        }
        
        if(maxsum <= K) {
            return;
        }
        
        if(n==1) {
            //  Create a clause
            ArrayList<Long> c = new ArrayList<Long>();
            for(int i = 0; i < Q.get(0).size(); i++) {
                if(Q.get(0).get(i) >= K) {
                    c.add(X.get(0).get(i));
                }
            }
            satModel.addClause(c);
            return;
        }
        
        satModel.addClause(-addPolynomialWatchdog(Q,X,K,useSorter,satModel));
    }
    
    
    //  The local variant has stronger propagation but is larger.
    public static void addAMOPBLocalPolynomialWatchdog(ArrayList<ArrayList<Integer>> Q, ArrayList<ArrayList<Long>> X, int K, boolean useSorter, Sat satModel) throws IOException {
        if(K==0) {
            for(ArrayList<Long> v : X) {
                for(long l : v) {
                    satModel.addClause(-l);
                }
            }
            return;
        }
        
        else if(K < 0){
            satModel.addClause(-satModel.getTrue());
            return;
        }
        
        int n = Q.size();
        
        int maxsum = 0;
        for(int i = 0; i < n; i++) {
            maxsum += Collections.max(Q.get(i));
        }
        
        if(maxsum <= K) {
            return;
        }
        
        if(n==1) {
            ArrayList<Long> c = new ArrayList<>();
            for(int i = 0; i < Q.get(0).size(); i++) {
                if(Q.get(0).get(i) >= K) {
                    c.add(X.get(0).get(i));
                }
            }
            satModel.addClause(c);
            return;
        }
        
        for(int i = 0; i < n; i++) {
            ArrayList<ArrayList<Integer>> Q2 = new ArrayList<>();  // = Q;
            for(int j=0; j<X.size(); j++) {
                ArrayList<Integer> tmp=new ArrayList<Integer>();
                copyArrayList(Q.get(j), tmp);
                Q2.add(tmp);
            }
            
            ArrayList<ArrayList<Long>> X2 = new ArrayList<>();  //= X;
            for(int j=0; j<X.size(); j++) {
                ArrayList<Long> tmp=new ArrayList<Long>();
                copyArrayList(X.get(j), tmp);
                X2.add(tmp);
            }
            
            Q2.set(i, Q2.get(Q2.size()-1));
            Q2.remove(Q2.size()-1);
            
            X2.set(i, X2.get(X2.size()-1));
            X2.remove(X2.size()-1);
            
            for(int j = 0; j < Q.get(i).size(); j++) {
                HashMap<Integer, Long> watchdog = new HashMap<>();   //  Pointless. Was probably a cache at some point. 
                if(!watchdog.containsKey(Q.get(i).get(j))) {
                    watchdog.put(Q.get(i).get(j), addPolynomialWatchdog(Q2,X2,K-Q.get(i).get(j),useSorter, satModel));
                }
                satModel.addClause(-watchdog.get(Q.get(i).get(j)), -X.get(i).get(j));
            }
        }
    }
    
    private static Pair<Long,Long> addTwoComparator(long x1, long x2, boolean leqclauses, boolean geqclauses, Sat satModel) throws IOException {
        long y1 = satModel.createAuxSATVariable();
        long y2 = satModel.createAuxSATVariable();
        
        if(leqclauses) {
            satModel.addClause(-x1, y1);
            satModel.addClause(-x2, y1);
            satModel.addClause(-x1, -x2, y2);
        }
        
        if(geqclauses) {
            satModel.addClause(x1, -y2);
            satModel.addClause(x2, -y2);
            satModel.addClause(x1, x2, -y1);
        }
        
        return new Pair<Long, Long>(y1, y2);
    }
    
    private static void addQuadraticMerge(ArrayList<Long> x1, ArrayList<Long> x2, ArrayList<Long> y, Sat satModel) throws IOException {
        if(x1.isEmpty()) {
            copyArrayList(x2, y);
        }
        else if(x2.isEmpty()) {
            copyArrayList(x1, y);
        }
        else {
            resizeArrayList(y, x1.size()+x2.size());
            
            for(int i = 0; i < x1.size() + x2.size(); i++) {
                y.set(i, satModel.createAuxSATVariable());
            }
            for(int i = 0; i < x1.size(); i++) {
                satModel.addClause(-x1.get(i), y.get(i));
                for(int j = 0; j < x2.size(); j++) {
                    satModel.addClause(-x1.get(i), -x2.get(j), y.get(i+j+1));
                }
            }
            for(int i = 0; i < x2.size(); i++) {
                satModel.addClause(-x2.get(i), y.get(i));
            }
        }
    }
    
    private static void addMerge(ArrayList<Long> x1, ArrayList<Long> x2, ArrayList<Long> y, boolean leqclauses, boolean geqclauses, Sat satModel) throws IOException {
        int a = x1.size();
        int b = x2.size();
        
        if(a==0 && b==0) {
            y.clear();
            return;
        }
        
        resizeArrayList(y, a+b);
        
        if(a==1 && b==1) {
            Pair<Long, Long> p=addTwoComparator(x1.get(0),x2.get(0),leqclauses,geqclauses,satModel);
            y.set(0, p.getFirst());
            y.set(1, p.getSecond());
        }
        else if(a == 0) {
            copyArrayList(x2, y);
        }
        else if(b == 0) {
            copyArrayList(x1, y);
        }
        else {
            ArrayList<Long> x1even=new ArrayList<Long>();
            ArrayList<Long> x1odd=new ArrayList<Long>();
            ArrayList<Long> x2even=new ArrayList<Long>();
            ArrayList<Long> x2odd=new ArrayList<Long>();
            
            for(int i = 0; i < a-1; i+=2) {
                x1even.add(x1.get(i));
                x1odd.add(x1.get(i+1));
            }
            if(a%2==1) {
                x1even.add(x1.get(a-1));
            }
            
            for(int i = 0; i < b-1; i+=2) {
                x2even.add(x2.get(i));
                x2odd.add(x2.get(i+1));
            }
            if(b%2==1) {
                x2even.add(x2.get(b-1));
            }
            
            ArrayList<Long> zeven = new ArrayList<Long>();
            ArrayList<Long> zodd = new ArrayList<Long>();
            
            addMerge(x1even, x2even,zeven,leqclauses,geqclauses, satModel);
            addMerge(x1odd, x2odd,zodd,leqclauses,geqclauses, satModel);
            
            ArrayList<Long> z=new ArrayList<Long>(a+b);
            for(int i=0; i<a+b; i++) z.add(0L);  //  Initialise z
            
            if(a%2==0) {
                if(b%2==0) {
                    for(int i = 0; i < (a+b)/2; i++) {
                        z.set(2*i, zeven.get(i));
                    }
                    
                    for(int i = 0; i < (a+b)/2; i++) {
                        z.set(2*i + 1, zodd.get(i));
                    }
                    
                    y.set(0, z.get(0));
                    y.set(a+b-1, z.get(a+b-1));
                    for(int i = 1; i < a+b-2; i+=2) {
                        Pair<Long, Long> p = addTwoComparator(z.get(i),z.get(i+1),leqclauses,geqclauses, satModel);
                        y.set(i, p.getFirst());
                        y.set(i+1, p.getSecond());
                    }
                }
                else {
                    for(int i = 0; i < (a+b)/2 + 1; i++) {
                        z.set(2*i, zeven.get(i));
                    }
                    
                    for(int i = 0; i < (a+b)/2; i++) {
                        z.set(2*i + 1, zodd.get(i));
                    }
                    
                    y.set(0, z.get(0));
                    for(int i = 1; i < a+b-1; i+=2) {
                        Pair<Long, Long> p = addTwoComparator(z.get(i),z.get(i+1),leqclauses,geqclauses, satModel);
                        y.set(i, p.getFirst());
                        y.set(i+1, p.getSecond());
                    }
                }
            }
            else { //a%2==1
                if(b%2==0) {
                    addMerge(x2,x1,y,leqclauses,geqclauses,satModel);
                }
                else{
                    for(int i = 0; i < (a+1)/2; i++) {
                        z.set(2*i, zeven.get(i));
                    }
                    for(int i = 0; i < (b+1)/2; i++) {
                        z.set(a + 2*i, zeven.get((a+1)/2 + i));
                    }
                    
                    for(int i = 0; i < a/2; i++) {
                        z.set(2*i+1, zodd.get(i));
                    }
                    for(int i = 0; i < b/2; i++) {
                        z.set(a + 2*i+1, zodd.get(a/2 + i));
                    }
                    
                    y.set(0, z.get(0));
                    y.set(a+b-1, z.get(a+b-1));
                    for(int i = 1; i < a+b-2; i+=2) {
                        Pair<Long, Long> p = addTwoComparator(z.get(i),z.get(i+1),leqclauses,geqclauses, satModel);
                        y.set(i, p.getFirst());
                        y.set(i+1, p.getSecond());
                    }
                }
            }
        }
    }

/*

void SMTFormula::addTotalizer(const std::vector<literal> &x, std::vector<literal> &y){

	int n = x.size();

	if(n==0){
		y.clear();
		return;
	}
	if(n==1){
		y = x;
		return;
	}

	std::vector<literal> * tree = new std::vector<literal> [2*n-1];

	//Fill tree nodes with coefficients
	for(int i = 0; i < n; i++){
		int idx = n-1+i;
		tree[idx].resize(1);
		tree[idx][0] = x[i];
	}

	for(int i = n-2; i >= 0; i--){
		int ls = tree[lchild(i)].size();
		int rs = tree[rchild(i)].size();
		tree[i].resize(ls + rs);
		for(int j = 0; j < ls + rs; j++)
			tree[i][j] = newBoolVar();

		for(int j = 0; j < ls; j++){
			addClause(!tree[lchild(i)][j] | tree[i][j]);
			for(int k = 0; k < rs; k++)
				addClause(!tree[lchild(i)][j] | !tree[rchild(i)][k] | tree[i][j+k+1]);
		}
		for(int k = 0; k < rs; k++)
			addClause(!tree[rchild(i)][k] | tree[i][k]);
	}

	y = tree[0];

	delete [] tree;
}


*/

    private static void addSorting(ArrayList<Long> x, ArrayList<Long> y, boolean leqclauses, boolean geqclauses, Sat satModel) throws IOException {
        //Codifies a mergesort
        int n = x.size();
        
        if(n==0) {
            y.clear();
            return;
        }
        
        if(n==1) {
            copyArrayList(x, y);
        }
        else if(n==2){
            Pair<Long,Long> p=addTwoComparator(x.get(0),x.get(1),leqclauses,geqclauses,satModel);
            y.clear();
            y.add(p.getFirst());
            y.add(p.getSecond());
        }
        else{
            ArrayList<Long> z1=new ArrayList<Long>();
            ArrayList<Long> z2=new ArrayList<Long>();
            
            ArrayList<Long> x1 = new ArrayList<Long>(x.subList(0, n/2));
            ArrayList<Long> x2 = new ArrayList<Long>(x.subList(n/2, n));
            
            addSorting(x1,z1,leqclauses,geqclauses, satModel);
            addSorting(x2,z2,leqclauses,geqclauses, satModel);
            addMerge(z1,z2,y,leqclauses,geqclauses, satModel);
        }
    }
    
    //  k=0 should be most significant bit or least? Must be least.
    private static boolean nthBit(int x, int k) {
        return (((x >>> k) & 1) == 1);
    }
    
    private static int floorlog2(int n){
        if(n <= 0) throw new IllegalArgumentException();
        int log1 = 31 - Integer.numberOfLeadingZeros(n);
        
        int log2 = (int) Math.floor(Math.log(n)/Math.log(2));
        assert log1==log2;
        return log1;
    }
    
    private static int exp2(int n) {
        if(n==0) return 1;
        return 1 << n;
    }
    
    public static <T> void copyArrayList(ArrayList<T> a, ArrayList<T> b) {
        b.clear();
        for(int i=0; i<a.size(); i++) {
            b.add(a.get(i));
        }
    }
    
    private static void resizeArrayList(ArrayList<Long> a, int n) {
        while(a.size()>n) {
            a.remove(a.size()-1);
        }
        while(a.size()<n) {
            a.add(0L);
        }
    }
}
