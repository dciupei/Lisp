#|
# Ugh... CMUCL doesn't provide an interpreter that's usable with a hash-bang
#   (probably because they hate UNIX for killing Lisp machines or something),
#   so we have to do this awful hack to make this file interpretable.
# Don't worry too much if this doesn't make sense;
#   it's supposed to be ridiculous.

exec lisp -batch -quiet -load "$0" -eval '(main)' -eval '(quit)'
|#

#-quicklisp (let ((quicklisp-init (merge-pathnames "quicklisp/setup.lisp"
                                                   (user-homedir-pathname))))
              (when (probe-file quicklisp-init)
                (load quicklisp-init)))

#-quicklisp (load "lib/quicklisp.lisp")
#-quicklisp (quicklisp-quickstart:install)

(load "3sat.lisp")

(with-open-file (s "/dev/null" :direction :output :if-exists :append)
  (let ((*standard-output* s))
    (ql:quickload :prove)))
(setf prove:*default-reporter* :tap)
(prove:plan 9)

(defun my-sort (l)
  (sort (copy-list l) #'string< :key #'write-to-string))

(defvar *score-vars* '(A B C D E F G H I J))

(defvar *score-clauses*
  '((F (NOT B) E) (C (NOT D) E) ((NOT G) F (NOT B)) (D C (NOT A)) (D F B)
    (D (NOT I) (NOT E)) ((NOT H) E I) ((NOT G) F I) (C F (NOT H)) (J G (NOT A))
    ((NOT H) E (NOT A)) (A (NOT F) E) ((NOT G) (NOT E) B) (E (NOT D) (NOT I))
    ((NOT G) I E) ((NOT G) (NOT B) E) (J D (NOT F)) (F (NOT H) E) (D (NOT H) E)
    ((NOT H) (NOT B) C) ((NOT E) I (NOT D)) (B (NOT F) (NOT A)) (E (NOT I) J)
    (E (NOT A) I) (D (NOT F) (NOT H)) (A H D) ((NOT D) G (NOT J)) (F D (NOT A))
    (C D F) ((NOT A) (NOT H) E)))

(defvar *score-state*
  '((A NIL) (B T) (C NIL) (D NIL) (E NIL) (F T) (G T) (H NIL) (I T) (J NIL)))

(defvar *score-unsat-clauses*
  '((A (NOT F) E) ((NOT G) (NOT B) E) (J D (NOT F)) (E (NOT I) J) (A H D)))

(defvar *score-good-state*
  '((A NIL) (B T) (C T) (D NIL) (E T) (F T) (G T) (H NIL) (I T) (J T)))

(defvar *hard-vars* '(A B C D E F G H I J K L M N O P))

(defvar *hard-soln*
  '((A T) (B T) (C T) (D T) (E T) (F T)
    (G NIL) (H NIL) (I NIL) (J NIL) (K T)
    (L T) (M NIL) (N T) (O NIL) (P T)))

(defvar *hard-clauses*
  '(((NOT B) (NOT M) O) ((NOT O) K (NOT J)) (B I J) (B C (NOT J))
    ((NOT I) P (NOT A)) (L A J) ((NOT G) L F) (A K (NOT M)) ((NOT F) D H)
    (P (NOT I) C) (K (NOT O) (NOT D)) ((NOT I) E D) ((NOT A) E (NOT P))
    ((NOT I) K P) ((NOT H) D A) (C B (NOT M)) (P (NOT F) B) ((NOT C) (NOT A) F)
    (M (NOT H) P) (D P C) ((NOT K) F P) (F (NOT I) P) (F O A) (F (NOT J) (NOT H))
    (J (NOT G) (NOT C)) ((NOT L) (NOT H) N) ((NOT J) (NOT N) (NOT P))
    ((NOT I) D (NOT K)) ((NOT A) (NOT J) (NOT I)) (D B P) (L E B) ((NOT P) E G)
    (E O (NOT C)) ((NOT M) E (NOT A)) (C I (NOT D)) (F (NOT O) K) ((NOT L) J P)
    (K N (NOT M)) (L (NOT O) P) ((NOT H) O I) (L D N) ((NOT M) L P) ((NOT L) I N)
    ((NOT I) (NOT E) (NOT F)) ((NOT D) (NOT J) (NOT P)) ((NOT I) B L)
    (D P (NOT J)) (O C N) (C D (NOT I)) ((NOT I) (NOT O) L) (E N C) (F A L)
    (L E (NOT H)) (F (NOT N) J) (K B (NOT D)) ((NOT I) D (NOT P)) (N K (NOT I))
    ((NOT O) L D) (C K (NOT G)) ((NOT K) D (NOT E)) ((NOT N) D (NOT G))
    ((NOT I) (NOT G) D) (D K (NOT G)) ((NOT B) A (NOT K)) (P (NOT A) (NOT D))
    (B (NOT I) D) (F (NOT J) (NOT N)) ((NOT L) N M) (L (NOT A) P)
    (P (NOT E) (NOT B)) (K C N) ((NOT C) J (NOT H)) (K P (NOT H)) (J D M)
    (N (NOT P) A) (F B E) ((NOT B) (NOT G) (NOT K)) (P M K) ((NOT H) (NOT L) E)
    ((NOT N) K (NOT A)) ((NOT A) B (NOT F)) (A (NOT J) (NOT O)) ((NOT D) A I)
    (A I O) (M (NOT F) K) (E (NOT P) (NOT A)) ((NOT J) (NOT H) D)
    (B (NOT J) (NOT H)) ((NOT H) (NOT G) (NOT J)) (F A C) (K (NOT H) (NOT J))
    ((NOT E) (NOT B) N) ((NOT D) (NOT C) N) (B N L) ((NOT L) (NOT J) (NOT N))
    ((NOT G) (NOT C) I)))

(defun score-eval-var (var state)
  (cond
    ((eq var (caar state)) (cadar state))
    ((not state) (error (format nil "Undefined var: ~a" var)))
    (t (score-eval-var var (cdr state)))))

(defun score-eval-clause (clause state)
  (cond
    ((null clause) nil)
    ((atom (car clause))
     (or (score-eval-var (car clause) state)
         (score-eval-clause (cdr clause) state)))
    (t (or (not (score-eval-var (cadar clause) state))
           (score-eval-clause (cdr clause) state)))))

(defun score-satisfied (clauses state)
  (or (null clauses)
      (and (score-eval-clause (car clauses) state)
           (score-satisfied (cdr clauses) state))))

(defun score-unsat-clauses (clauses state)
  (cond
    ((null clauses) nil)
    ((score-eval-clause (car clauses) state)
     (score-unsat-clauses (cdr clauses) state))
    (t (cons (car clauses)
             (score-unsat-clauses (cdr clauses) state)))))

(defun test-eval-var ()
  (let ((state '((A T) (B NIL) (C NIL) (D T) (Z NIL))))
    (prove:subtest (format nil "eval-var with state = ~a" state)
      (dolist (p state)
        (prove:is (eval-var (car p) state) (cadr p) (string (car p)))))))

(defun test-eval-clause ()
  (let ((state '((A T) (B NIL) (C NIL) (D T) (Z T))))
    (prove:subtest (format nil "eval-clause with state = ~a" state)
      (let ((clauses
             (list
              (list t '(A (NOT B) (NOT C) D Z))
              (list nil '((NOT A) B  C (NOT D) (NOT Z)))
              (list t '((NOT A) B  C (NOT D) Z))
              (list t '((NOT A) (NOT B)  C (NOT D) (NOT Z)))
              (list t '((NOT A) B  C D (NOT Z))))))
        (loop for (answer clause) in clauses
           do (prove:is (eval-clause clause state) answer (write-to-string clause)))))))

(defun test-get-vars ()
  (let ((clause '((NOT U) V  W (NOT X) (NOT Y))))
    (prove:is (delete-duplicates (my-sort (get-vars clause)))
              '(u v w x y)
              (format nil "get-vars with clause = ~a" clause))))

(defun test-get-all-vars ()
  (prove:is (my-sort (get-all-vars *score-clauses*))
            *score-vars*
            (format nil "get-all-vars (see *score-clauses* in source for clauses)")))

(defun test-unsat-clauses ()
  (prove:is (my-sort (unsat-clauses *score-clauses* *score-state*))
            (my-sort *score-unsat-clauses*)
            (format nil "unsat-clauses (see *score-clauses* and *score-state* in source for clauses & state)")))

(defun test-flip-var ()
  (let ((state (my-sort '((Q t) (W nil) (E nil) (R t) (Y t)))))
    (prove:subtest (format nil "flip-var with state = ~a" state)
      (prove:is (my-sort (flip-var 'w state))
                (my-sort '((Q t) (W t) (E nil) (R t) (Y t)))
                "Flip W")
      (prove:is (my-sort (flip-var 'r state))
                (my-sort '((Q t) (W nil) (E nil) (R nil) (Y t)))
                "Flip R"))))

(defun test-get-better-neighbor ()
  (prove:ok (< (length (score-unsat-clauses *score-clauses*
                                            (car
                                             (get-better-neighbor
                                              *score-clauses* *score-state* *score-vars*
                                              (length *score-unsat-clauses*)))))
               (length *score-unsat-clauses*))
            "get-better-neighbor (see *score-clauses* in source for clauses)"))

(defun test-simple-hill-climb ()
  (prove:ok
   (let* ((u (score-unsat-clauses *score-clauses* *score-good-state*))
          (st (simple-hill-climb *score-clauses* *score-good-state* 10 u)))
     (and st (score-satisfied *score-clauses* st)))))

(defun my-unsat-clauses (clauses state)
  (cond
    ((null clauses) nil)
    ((eval-clause (car clauses) state)
     (my-unsat-clauses (cdr clauses) state))
    (t (cons (car clauses)
             (my-unsat-clauses (cdr clauses) state)))))

(defun my-get-random-state (vars)
  (cond
    ((null vars) nil)
    (t (cons (list (car vars)
                   (= (random 2) 0))
             (my-get-random-state (cdr vars))))))

(defun test-simple-hill-climb-harder ()
  (prove:ok
   (loop
      for i from 1 to 20
      for start-state = (my-get-random-state *hard-vars*)
      for start-unsat-clauses = (my-unsat-clauses *hard-clauses* start-state)
      for end-state = (simple-hill-climb *hard-clauses* start-state 20 start-unsat-clauses)
      ; do (format t "Try #~a~%" i)
      when (and end-state (score-satisfied *hard-clauses* end-state))
      do (return t)
      finally (return nil))
   "simple-hill-climb with harder clauses"))

(defun main ()
  (test-eval-var)
  (test-eval-clause)
  (test-get-vars)
  (test-get-all-vars)
  (test-unsat-clauses)
  (test-flip-var)
  (test-get-better-neighbor)
  (test-simple-hill-climb)
  (test-simple-hill-climb-harder))
