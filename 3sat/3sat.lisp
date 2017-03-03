;David Ciupei
;CS355 Project #4

(defun eval-var (var state)   
  ;; goes through the list checking each variable if found 
  ;; returns its value
  (cond 
   (( atom state) nil)
   ((eql(caar state) var) (cadr (car state)))  
   (t(eval-var var (cdr state)))))

(defvar *clause* '(a (not b) c))


(defun eval-clause (clause state)
;; goes through checking the single variables and the 'not variables
;; and evaluating them to return T or nil 
  (cond
    ((null clause) nil)
    ((and (atom (car clause)) (eq (eval-var (car clause) state)t)))
    ((and (listp (car clause)) (eq (not (eval-var (cadar clause) state)) t))) 
    (t (eval-clause (cdr clause) state)) ))


(defun flatten (list)
  (cond
   ((null list) nil) ; empty list
   ((consp (car list)) ; first element is a cons
    (append
     (flatten (car list))
     (flatten (cdr list)) ) )
   (t ; first element is an atom
    (cons (car list) (flatten (cdr list))) ) ) )

(defun get-vars (clause)
  ;; removes not from clause and removes the paranthesis with flatten
  (remove 'not (flatten clause)))

(defvar *clauses* '((a (not b) c) (a (not b) (not c)) (a (not b) d)))

(defun get-all-vars (clauses) 
  ;;calls get vars then remove duplicates 
  (let((allvars (get-vars clauses)))  
    (remove-duplicates (flatten allvars))))
  
    
(defun unsat-clauses (clauses state)
  ;; goes through the clauses and makes a list of the clauses that 
  ;; are not satisfying to the state
    (cond 
     ((null clauses) nil)
      ((eq (eval-clause (car clauses) state) 'nil) 
        (cons (car clauses)(unsat-clauses (cdr clauses) state)))
      (t(unsat-clauses (cdr clauses) state))))

          
(defun flip-var (var state)
  ;; flips the value of the var being passed through the function
  (cond 
   ((null state) nil)
   ((eq var (caar state))
    (cons (list var (not (cadar state)))(cdr state)))
   (t(cons (car state)(flip-var var (cdr state))))))

(defun get-better-neighbor (clauses state vars max-num-unsat)
  ;;first checks if list is nil 
  ;;returns the list if the length of unsat is less then 
  ;;max-num-unsat if not recurses the rest of the list
  (cond
   ((null vars) nil)
      (t(let*((FlipV (flip-var(car vars) state))
	      (unsat (unsat-clauses clauses FlipV)))
	  
	  (cond
	((< (length unsat) max-num-unsat)(list FlipV unsat))
	(t(get-better-neighbor clauses state (cdr vars) max-num-unsat)))))))


(defun simple-hill-climb (clauses state dist unsat)
  ;;this function will get the better neighbor while the distance is decremented
  ;;if the distance is 0 it will return nil if not checks if unsat is empty and 
  ;;returns the state
  (cond 
   ((= dist 0) nil)
   ((null unsat) state)
   (t (let* ((vars (get-all-vars clauses))
	     (getB (get-better-neighbor clauses state vars
						  (length unsat) )) )
	(simple-hill-climb clauses (car getB) (- dist 1) (cadr getB))))))
