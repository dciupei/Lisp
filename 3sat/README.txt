Common Lisp 3SAT solver using simple hill climbing.

Name: David Ciupei
Email: david.ciupei@wsu.edu
SID: 11383576

	To run this code run clisp then load the function (load “3sat.lisp”). After that set the state ‘(setf *state* ’((a nil) (b t) (c t) (d nil)))’ then run each function for example  ‘(eval-var ’b *state*)’ or push the project onto gitlab to see what each function does or returns.

	3-sat will efficiently check to see if a solution is correct. In the first function (eval-var) a variable is passed through. The first thing it checks is is the list if empty if not it checks if the variable is in the list. If its in the list returns the truth value if not recurses through the list. In the second function (eval-clause) it will go through comparing the each element in the clause with each element in the state and if one of them evaluate to true then the whole clause if true if not returns nil. In the next function (get-vars) it will just go through the clause and will only return the variables that are being used. Get-all-vars is the same thing except it will delete any duplicates. Unsat-Clauses will check the clauses and compare them with the state and it will return the clauses that do not satisfy (that would return nil). Flip-var will get the passed in variable and go through the state and flip the truth value. Get-better-neighbor will check the each element to a given state that yields fewer unsatisfied clauses then will return the list of unsatisfied clauses with the better at the front. The last function simple-hill-climb will begin at a given start state and will continue looking for a better neighbors until it finds the solution. If the dist = 0 then it will return nil if not will return the state.  

README.txt ........... This file.
3sat.lisp ............ Lisp functions required by the project.
t/00-readme.t ........ Checks README for name, email, etc
t/01-3sat.t .......... Checks 3sat.lisp for correctness
.gitlab-ci.yml ....... Contains metadata for GitLab CI
.proverc ............. Configuration file for tests
lib/quicklisp.lisp ... Package manager (used in tests)
