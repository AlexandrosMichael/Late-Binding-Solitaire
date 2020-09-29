# Late Binding Solitaire - Constraint Programming

In this project we were required to model and solve the game of Late Binding Solitaire, a variant of Solitaire which is a family of single-player card games. The model is formulated in Essence Prime and Savilerow is then used to translate it into the language of a constraint solver such as Minion. Following that, we were required to evaluate the performance of our model on 25 instances (19 solvable and 6 unsolvable), using metrics such as the SolverNodes, SolverSolveTime and Savile Row TotalTime. Furthermore, we were require to use an instance generator to produce more problem instances and explore the lengths of instance (where length n is the number of cards) to which our model would scale.

## Scripts
In order to automate the process of running Savilerow for each instance, I’ve created a number of scripts.
* run_solvable_linux.sh: Runs all the provided, solvable instances of the problem.
* run_solvable.sh: Same as above but for macOS.
* run_unsolvable_linux.sh: Runs all the provided, unsolvable instances
of the problem.
* run_unsolvable.sh: Same as above but for macOS.
Note: in order to run these scripts you may need to give execute privileges to them using:
```bash
chmod +x <script_name>
```

## Report

See CS4402_P1.pdf for a complete report, containing installation and usage instructions.
