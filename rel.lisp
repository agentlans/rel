;; Library for binary relations as represented by association lists

;; Copyright 2022 Alan Tseng
;; 
;; This program is free software: you can redistribute it and/or modify it 
;; under the terms of the GNU Lesser General Public License as published by the 
;; Free Software Foundation, either version 3 of the License, or (at your 
;; option) any later version.
;; 
;; This program is distributed in the hope that it will be useful, but WITHOUT 
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or 
;; FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License 
;; for more details.
;; 
;; You should have received a copy of the GNU Lesser General Public License 
;; along with this program. If not, see <https://www.gnu.org/licenses/>.

(defpackage :rel
  (:use :cl)
  (:export
   ;; Basic operations on relations
   :domain
   :range
   :converse
   :identity-relation
   :complement-relation
   :lookup
   :reverse-lookup
   :composition
   ;; Properties
   :one-to-many?
   :many-to-one?
   :injective?
   :surjective?
   :bijective?
   :reflexive?
   :symmetric?
   :transitive?
   ;; Restrict domain and range
   :restriction
   :left-restriction
   :right-restriction
   ;; Helpers
   :unique
   :in?
   :has-duplicate?
   :product
   ))
(in-package :rel)

(defun unique (s)
  "Only keeps non-duplicated elements of s."
  (remove-duplicates s :test #'equal))

(defun unique-when (flag x)
  "Uniquify only when flag is T."
  (if flag
      (unique x)
      x))

;; The domain and range of a binary relation
(defun domain (rel &optional (make-unique t))
  "Domain of the relation rel."
  (unique-when make-unique
	       (mapcar #'car rel)))

(defun range (rel &optional (make-unique t))
  "Range of the relation rel."
  (unique-when make-unique
	       (mapcar #'cdr rel)))

(defun converse (rel)
  "{(x,y) : yRx}"
  (loop for (a . b) in rel
	collect (cons b a)))

(defun identity-relation (s)
  "Identity relation of x in S to itself."
  (loop for x in s
	collect (cons x x)))

(defun product (s1 s2)
  "Cartesian product of two sets.
Returns an alist."
  (loop for x in s1
	append (loop for y in s2
		     collect
		     (cons x y))))

(defmacro filter-mac (crit)
  "Filters the pairs in relation rel
according to some criterion."
  `(loop for (x . y) in rel
	 if ,crit
	   collect (cons x y)))

(defun in? (x s)
  (member x s :test #'equal))

(defun restriction (rel s)
  "{(x,y) : x in S, y in S"
  (filter-mac (and (in? x s)
		   (in? y s))))

(defun left-restriction (rel s)
  "{(x,y) : xRy, x in S}"
  (filter-mac (in? x s)))

(defun right-restriction (rel s)
  "{(x,y) : xRy, y in S}"
  (filter-mac (in? y s)))

(defun lookup (rel x)
  "Returns the set of y that x maps to. {y : xRy}"
  (range (left-restriction
	  rel (list x))))
;; (lookup '((a . b) (a . c) (b . d)) 'a)

(defun reverse-lookup (rel y)
  "Returns the set of x that map to y. {x : xRy}"
  (range (right-restriction
	  rel (list y))))

(defun composition (r1 r2)
  "Composition of r1 and r2.
{(x,y) : exists c such that r1(x,c) and r2(c,y)}"
  (let ((common (intersection
		 (range r1) (domain r2)
		 :test #'equal)))
    (loop for c in common
	  append (product
		  (domain (right-restriction r1 (list c)))
		  (range (left-restriction r2 (list c)))))))
;; (composition '((a . 1) (b . 2)) '((1 . -1) (1 . one) (3 . -3)))

(defun complement-relation (rel)
  "{(x,y) : x in domain(Rel), y in range(Rel), not Rel(x,y)}
Note: uses a dumb O(n^4) algorithm where n is the number of elements."
  (let ((xs (domain rel))
	(ys (range rel)))
    (set-difference (product xs ys) rel :test #'equal)))

(defun is-duplicated? (x lst)
  "Whether x occurs more than once in the list."
  (> (count x lst :test #'equal) 1))

(defun has-duplicate? (lst)
  "Whether there are any duplicate elements in lst."
  (loop for x in lst
	thereis (is-duplicated? x lst)))

(defun one-to-many? (rel)
  "Whether there exists an element that maps to many elements."
  (has-duplicate?
   (domain (unique rel) nil)))
;; (one-to-many? '((a . 1) (a . 2))) ;=> T
;; (one-to-many? '((a . 1) (a . 1))) ;=> NIL

(defun many-to-one? (rel)
  "Whether there are multiple x that map to the same y."
  (has-duplicate?
   (range (unique rel) nil)))
;; (many-to-one? '((a . 1) (b . 1))) ;=> T
;; (many-to-one? '((a . 1) (b . 2))) ;=> NIL
;; (many-to-one? '((a . 1) (a . 2))) ;=> NIL
;; (many-to-one? '((a . 1) (a . 2) (b . 2))) ;=> T

(defun injective? (rel)
  "Whether Rel maps distinct elements to distinct elements."
  (not (many-to-one? rel)))
;; (injective? '((a . 1) (b . 1) (c . 2))) ;=> NIL
;; (injective? '((a . 1) (b . 3) (c . 2))) ;=> T

(defun surjective? (rel &optional (codomain nil))
  "Whether every element in codomain is mapped from some x."
  (if (not codomain)
      t ; trivial because y is empty. Don't need to compute the range of rel.
      (let ((rely (range rel)))
	;; Shouldn't have any y outside the codomain
	(assert (subsetp rely codomain :test #'equal))
	;; Whether codomain contains any elements not in the range.
	(not (set-difference codomain rely :test #'equal)))))

(defun bijective? (rel &optional (codomain nil))
  "Whether Rel represents a bijective function."
  (and (not (one-to-many? rel)) ; i.e. like a function
       (injective? rel)
       (surjective? rel codomain)))

(defun underlying (rel)
  "Returns the underlying set of an endorelation."
  (union (domain rel) (range rel) :test #'equal))

(defun reflexive? (rel)
  "Whether each element is related to itself."
  (subsetp (identity-relation
	    (underlying rel))
	   rel :test #'equal))

(defun symmetric? (rel)
  "Whether (x,y) in Rel implies (y,x) in Rel."
  (loop for (x . y) in rel
	always (in? (cons y x) rel)))

(defun transitive? (rel)
  "Whether Rel is transitive. That is, for all
a, b, c in Rel, Rel(a,b) and Rel(b,c) imply Rel(a,c)."
  (subsetp (composition rel rel) rel
	   :test #'equal))
;; (transitive? '((a . b) (b . c) (a . c) (e . e))) ;=> T
;; (transitive? '((a . b) (b . d) (b . c))) ;=> NIL
