import java.util.*;

public class BTSolver
{

	// =================================================================
	// Properties
	// =================================================================

	private ConstraintNetwork network;
	private SudokuBoard sudokuGrid;
	private Trail trail;

	private boolean hasSolution = false;

	public String varHeuristics;
	public String valHeuristics;
	public String cChecks;

	// =================================================================
	// Constructors
	// =================================================================

	public BTSolver ( SudokuBoard sboard, Trail trail, String val_sh, String var_sh, String cc )
	{
		this.network    = new ConstraintNetwork( sboard );
		this.sudokuGrid = sboard;
		this.trail      = trail;

		varHeuristics = var_sh;
		valHeuristics = val_sh;
		cChecks       = cc;
	}

	// =================================================================
	// Consistency Checks
	// =================================================================

	// Basic consistency check, no propagation done
	private boolean assignmentsCheck ( )
	{
		for ( Constraint c : network.getConstraints() )
			if ( ! c.isConsistent() )
				return false;

		return true;
	}

	// =================================================================
	// Arc Consistency
	// =================================================================
	public boolean arcConsistency ( )
    {
        List<Variable> toAssign = new ArrayList<Variable>();
        List<Constraint> RMC = network.getModifiedConstraints();
        for(int i = 0; i < RMC.size(); ++i)
        {
            List<Variable> LV = RMC.get(i).vars;
            for(int j = 0; j < LV.size(); ++j)
            {
                if(LV.get(j).isAssigned())
                {
                    List<Variable> Neighbors = network.getNeighborsOfVariable(LV.get(j));
                    int assignedValue = LV.get(j).getAssignment();
                    for(int k = 0; k < Neighbors.size(); ++k)
                    {
                        Domain D = Neighbors.get(k).getDomain();
                        if(D.contains(assignedValue))
                        {
                            if(D.size() == 1)
                                return false;
                            if(D.size() == 2)
                                toAssign.add(Neighbors.get(k));
                            trail.push(Neighbors.get(k));
                            Neighbors.get(k).removeValueFromDomain(assignedValue);
                        }
                    }
                }
            }
        }
        if(!toAssign.isEmpty())
        {
            for(int i = 0; i < toAssign.size(); ++i)
            {
                Domain D = toAssign.get(i).getDomain();
                ArrayList<Integer> assign = D.getValues();
                trail.push(toAssign.get(i));
                toAssign.get(i).assignValue(assign.get(0));
            }
            return arcConsistency();
        }
        return network.isConsistent();
    }


	/**
	 * Part 1 TODO: Implement the Forward Checking Heuristic
	 *
	 * This function will do both Constraint Propagation and check
	 * the consistency of the network
	 *
	 * (1) If a variable is assigned then eliminate that value from
	 *     the square's neighbors.
	 *
	 * Note: remember to trail.push variables before you change their domain
	 *
	 * Return: a pair of a HashMap and a Boolean. The map contains the pointers to all MODIFIED variables, mapped to their MODIFIED domain. 
	 *         The Boolean is true if assignment is consistent, false otherwise.
	 */
	public Map.Entry<HashMap<Variable,Domain>, Boolean> forwardChecking ( )
	{
		HashMap<Variable,Domain> map= new HashMap<Variable,Domain>();
		List<Constraint> constraint_list= network.getModifiedConstraints();
		for(Constraint c: constraint_list)
		{
			for(Variable v:c.vars)
				if(v.isAssigned())
				{
					int val= v.getAssignment();
					List<Variable> Neighbors = network.getNeighborsOfVariable(v);
					// Removing the assigned value from each of neighbors domains
					for(Variable var:Neighbors)
					{
						if(var.getDomain().contains(val))
						{
							trail.push(var);
							var.removeValueFromDomain(val);
							if(var.getDomain().size()==0)
								return Pair.of(map,false);
							if(!map.containsKey(var))
								map.put(var,var.getDomain());
							else
								map.replace(var,var.getDomain());
						}
					}
				}
		}

		return Pair.of(map, true);
	}

	/**
	 * Part 2 TODO: Implement both of Norvig's Heuristics
	 *
	 * This function will do both Constraint Propagation and check
	 * the consistency of the network
	 *
	 * (1) If a variable is assigned then eliminate that value from
	 *     the square's neighbors.
	 *
	 * (2) If a constraint has only one possible place for a value
	 *     then put the value there.
	 *
	 * Note: remember to trail.push variables before you change their domain
	 * Return: a pair of a map and a Boolean. The map contains the pointers to all variables that were assigned during the whole 
	 *         NorvigCheck propagation, and mapped to the values that they were assigned. 
	 *         The Boolean is true if assignment is consistent, false otherwise.
	 */
	public Map.Entry<HashMap<Variable,Integer>,Boolean> norvigCheck ( )
	{

		Map.Entry<HashMap<Variable,Domain>, Boolean> fcheck=forwardChecking();
		Boolean ans= fcheck.getValue();
		HashMap<Variable,Integer> map= new HashMap<Variable,Integer>();
		if(!ans) return Pair.of(map, false);
		List<Constraint> constraint_list= network.getModifiedConstraints();

		for(Constraint c: constraint_list)
		{
			for(Variable v:c.vars)
			{
				if(!v.isAssigned()) {
					int[] boxes={v.row(),v.col(),v.block()};
					List<Variable> Neighbors = network.getNeighborsOfVariable(v);
					int [] counter= new int[sudokuGrid.getN()+1];
					ArrayList<Integer> d= v.getDomain().getValues();
					for(int z=0;z<3;z++) {
						Arrays.fill(counter, 0);
						for (Variable var : Neighbors) {
							int abc=-1;
							if(z==0) abc=var.row();
							else if(z==1) abc=var.col();
							else abc=var.block();
							if (abc == boxes[z]) {
								ArrayList<Integer> dom = var.getDomain().getValues();
								for (int i = 0; i < dom.size(); i++) {
									counter[dom.get(i)]++;
								}
							}
						}
						int value=-1;
						for(int x=1;x<counter.length;x++)
							if(counter[x]==0)
								value=x;
						Domain dom= v.getDomain();
						if (dom.contains(value)) {
							trail.push(v);
							v.assignValue(value);
							map.put(v, value);
							fcheck = forwardChecking();
							ans = fcheck.getValue();
							if(!ans) return Pair.of(map, false);
						}
					}
				}
			}
		}
		return Pair.of(map,true);
	}

	/**
	 * Optional TODO: Implement your own advanced Constraint Propagation
	 *
	 * Completing the three tourn heuristic will automatically enter
	 * your program into a tournament.
	 */
	private boolean getTournCC ( )
	{
		return false;
	}

	// =================================================================
	// Variable Selectors
	// =================================================================

	// Basic variable selector, returns first unassigned variable
	private Variable getfirstUnassignedVariable()
	{
		for ( Variable v : network.getVariables() )
			if ( ! v.isAssigned() )
				return v;

		// Everything is assigned
		return null;
	}

	/**
	 * Part 1 TODO: Implement the Minimum Remaining Value Heuristic
	 *
	 * Return: The unassigned variable with the smallest domain
	 */
	public Variable getMRV ( )
	{
		Variable next_var=null;
		int min= Integer.MAX_VALUE;
		//Iterate over all unassigned variables to find the one with maximum remaining values
		for( Variable v: network.getVariables())
		{
			if(!v.isAssigned())
			{
				if (min>v.getDomain().size())
				{
					min= v.getDomain().size();
					next_var= v;
				}

			}
		}
        return next_var;
	}

	/**
	 * Part 2 TODO: Implement the Minimum Remaining Value Heuristic
	 *                with Degree Heuristic as a Tie Breaker
	 *
	 * Return: The unassigned variable with the smallest domain and affecting the most unassigned neighbors.
	 *         If there are multiple variables that have the same smallest domain with the same number 
	 *         of unassigned neighbors, add them to the list of Variables.
	 *         If there is only one variable, return the list of size 1 containing that variable.
	 */
	public List<Variable> MRVwithTieBreaker ( )
	{
		Variable next_var=getMRV();
		List<Variable> mad= new LinkedList<Variable>();
		if(next_var==null)
		{
			mad.add(null);
			return mad;
		}
		final int size= next_var.getDomain().size();
		int degree=0;
		List<Variable> temp=new ArrayList<Variable>(network.getNeighborsOfVariable(next_var));
		for(Variable v: temp)
			if(!v.isAssigned()) degree++;
		mad.add(next_var);
		for(Variable v: network.getVariables())
		{
			if(!v.isAssigned() && v.getDomain().size()==size)
			{
				int count=0;
				List<Variable> temp1=new ArrayList<Variable>(network.getNeighborsOfVariable(v));
				for(Variable v1: temp1)
					if(!v1.isAssigned()) count++;
				if(count>degree) {
					degree = count;
					mad.clear();
				}
				if(count==degree){
					if(v!=next_var)
						mad.add(v);
				}
			}
		}
		return mad;
    }

	/**
	 * Optional TODO: Implement your own advanced Variable Heuristic
	 *
	 * Completing the three tourn heuristic will automatically enter
	 * your program into a tournament.
	 */
	private Variable getTournVar ( )
	{
		return null;
	}

	// =================================================================
	// Value Selectors
	// =================================================================

	// Default Value Ordering
	public List<Integer> getValuesInOrder ( Variable v )
	{
		List<Integer> values = v.getDomain().getValues();

		Comparator<Integer> valueComparator = new Comparator<Integer>(){

			@Override
			public int compare(Integer i1, Integer i2) {
				return i1.compareTo(i2);
			}
		};
		Collections.sort(values, valueComparator);
		return values;
	}

	/**
	 * Part 1 TODO: Implement the Least Constraining Value Heuristic
	 *
	 * The Least constraining value is the one that will knock the least
	 * values out of it's neighbors domain.
	 *
	 * Return: A list of v's domain sorted by the LCV heuristic
	 *         The LCV is first and the MCV is last
	 */
	public List<Integer> getValuesLCVOrder ( Variable v )
	{
		List<Integer> v_values = v.getDomain().getValues();
		List<Variable> Neighbors = network.getNeighborsOfVariable(v);
		Map<Integer, Integer> map= new TreeMap<Integer, Integer>();
		//Counting the neighbors that have particular assignment
		for(int val: v_values)
		{
			int count=0;
			for(Variable n: Neighbors)
			{
				if(n.getDomain().contains(val))
					count++;
			}
			map.put(val,count);
		}
		//Sorting
		/*
		//Alternate sorting code (return lcv_values)
		List<Map.Entry<Integer,Integer>> list = new LinkedList<Map.Entry<Integer, Integer>>(map.entrySet());
		Collections.sort(list, new Comparator<Map.Entry<Integer, Integer>>() {
			@Override
			public int compare(Map.Entry<Integer, Integer> o1, Map.Entry<Integer, Integer> o2) {
				if(o1.getValue()==o2.getValue())
					return(o1.getKey().compareTo(o2.getKey()));
				return (o1.getValue()).compareTo(o2.getValue());
			}
		});
		List<Integer> lcv_values = new ArrayList<Integer>();
		for(Map.Entry<Integer,Integer> item : list)
		{
			lcv_values.add(item.getKey());
		}
		*/
		List<Integer> lcv_values = new ArrayList<Integer>(v_values.size());
		for(int i:map.values())
			lcv_values.add(i);
		Collections.sort(lcv_values);
		v_values.clear();
		for(int j: lcv_values)
		{
			for(int i:map.keySet())
			{
				if(map.get(i)==j)
				{
					v_values.add(i);
					map.replace(i,-1);
				}
			}
		}
        return v_values;
	}

	/**
	 * Optional TODO: Implement your own advanced Value Heuristic
	 *
	 * Completing the three tourn heuristic will automatically enter
	 * your program into a tournament.
	 */
	public List<Integer> getTournVal ( Variable v )
	{
		return null;
	}

	//==================================================================
	// Engine Functions
	//==================================================================

	public void solve ( )
	{
		if ( hasSolution )
			return;

		// Variable Selection
		Variable v = selectNextVariable();

		if ( v == null )
		{
			for ( Variable var : network.getVariables() )
			{
				// If all variables haven't been assigned
				if ( ! var.isAssigned() )
				{
					System.out.println( "Error" );
					return;
				}
			}

			// Success
			hasSolution = true;
			return;
		}

		// Attempt to assign a value
		for ( Integer i : getNextValues( v ) )
		{
			// Store place in trail and push variable's state on trail
			trail.placeTrailMarker();
			trail.push( v );

			// Assign the value
			v.assignValue( i );

			// Propagate constraints, check consistency, recurse
			if ( checkConsistency() )
				solve();

			// If this assignment succeeded, return
			if ( hasSolution )
				return;

			// Otherwise backtrack
			trail.undo();
		}
	}

	public boolean checkConsistency ( )
	{
		switch ( cChecks )
		{
			case "forwardChecking":
				return forwardChecking().getValue();

			case "norvigCheck":
				return norvigCheck().getValue();

			case "tournCC":
				return getTournCC();

			default:
				return assignmentsCheck();
		}
	}

	public Variable selectNextVariable ( )
	{
		switch ( varHeuristics )
		{
			case "MinimumRemainingValue":
				return getMRV();

			case "MRVwithTieBreaker":
				return MRVwithTieBreaker().get(0);

			case "tournVar":
				return getTournVar();

			default:
				return getfirstUnassignedVariable();
		}
	}

	public List<Integer> getNextValues ( Variable v )
	{
		switch ( valHeuristics )
		{
			case "LeastConstrainingValue":
				return getValuesLCVOrder( v );

			case "tournVal":
				return getTournVal( v );

			default:
				return getValuesInOrder( v );
		}
	}

	public boolean hasSolution ( )
	{
		return hasSolution;
	}

	public SudokuBoard getSolution ( )
	{
		return network.toSudokuBoard ( sudokuGrid.getP(), sudokuGrid.getQ() );
	}

	public ConstraintNetwork getNetwork ( )
	{
		return network;
	}
}
