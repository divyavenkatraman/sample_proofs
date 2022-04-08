#|
Lab 10

In this lab we will define set intersection, a function that takes two
true-lists and returns a list of elements common to both lists,
without duplicates. We will define a tail-recursive function and we
will prove that the functions are equivalent, using the recipe for
reasoning about accumulator-based functions.

First, a review of some definitions and theorems we know.

|#

(definec app2 (x :tl y :tl) :tl
  (if (endp x)
      y
    (cons (car x) (app2 (cdr x) y))))

(definec rev2 (x :tl) :tl
  (if (endp x)
      x
    (app2 (rev2 (cdr x)) (list (car x)))))

(definec revt (x :tl acc :tl) :tl
  (if (endp x)
      acc
    (revt (cdr x) (cons (car x) acc))))

(definec rev* (x :tl) :tl
  (revt x nil))

(definec del-all (a :all X :tl) :tl
  (cond ((endp X) X)
        ((== a (car X))
         (del-all a (cdr X)))
        (t (cons (car X) (del-all a (cdr X))))))

(definec nodups (x :tl) :bool
  (v (endp (cdr x))
     (^ (! (in (car x) (cdr x)))
        (nodups (cdr x)))))

(property app2-associative (x :tl y :tl z :tl)
  (== (app2 (app2 x y) z)
      (app2 x (app2 y z))))

(property app2-nil (x :tl)
  (== (app2 x nil) x))

(property rev2-over-app2 (x :tl y :tl)
  (== (rev2 (app2 x y))
      (app2 (rev2 y) (rev2 x))))

(property rev2-rev2 (x :tl)
  (== (rev2 (rev2 x)) x))

(property revt-rev2 (x :tl acc :tl)
  (== (revt x acc)
      (app2 (rev2 x) acc)))

(property rev*-rev2 (x :tl)
  (== (rev* x)
      (rev2 x)))

; There is no reason for ACL2s to use the definition of rev* anymore.
(in-theory (disable rev*-definition-rule))

#|

Defining intersect using the recipe.

Part 1: Defining functions

1. Start with a function f. (intersect)

|#

(definec intersect (x :tl y :tl) :tl
  (cond ((endp x) nil)
        ((in (car x) y)
         (cons (car x)
               (intersect (del-all (car x) (cdr x))
                          (del-all (car x) y))))
        (t (intersect (cdr x) y))))

; Q1. What is a measure for intersect?
;     Make sure you can do the full termination proof.
;     Anything interesting?
;     We will only discuss this at a high-level in lab.
;     But, do the complete proof on your own. This is a good practice
;     problem. 

; Step 2 of Part 1:
;
; Define ft, a tail-recursive version of f with an accumulator. (intersectt)

(definec intersectt (x :tl y :tl acc :tl) :tl
  (cond ((endp x) acc)
        ((in (car x) y)
         (intersectt (del-all (car x) (cdr x))
                     (del-all (car x) y)
                     (cons (car x) acc)))
        (t (intersectt (cdr x) y acc))))

; Q2. What is a measure for intersectt?
;     Make sure you can do the full termination proof.
;     Anything interesting?
;     We will only discuss this at a high-level in lab.
;     But, do the complete proof on your own. This is a good practice
;     problem. 

;

; Step 3 of Part 1:
;
; Define f*, a non-recursive function that calls ft and is logically
; equivalent to f, i.e., this is a theorem (intersect*)
;
; hyps ⇒ (f* ...) = (f ...)

; Q3: define intersect* so that the phi1 (shown below) holds and make
; sure it runs in linear time.
(definec intersect* (x :tl y :tl) :tl
  (... (intersectt x y ...) ...))

; phi1:
(=> (^ (tlp x) (tlp y))
    (== (intersect* x y)
        (intersect x y)))

; Q4: prove phi1 (use the recipe!)


; Extra problem (not covered in lab)
; Q5: prove phi2 (use professional method)
; phi2: 

(=> (^ (tlp x) (tlp y))
    (nodups (intersect* x y)))
