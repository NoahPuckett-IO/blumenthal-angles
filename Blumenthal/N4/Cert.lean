/-!
Certificate checker. A certificate for "no `k`-clique in `P`" is a tree:
* `node cls kids`: `cls` is a colouring of `P` (list of colour classes, each a list of vertices);
  if `cls.length < k` there are no kids; otherwise the branch vertices are the members of
  `cls.drop (k-1)` in listed order, and `kids` certify the child problems
  `(P' ∩ N(v), k-1)` where `P'` is `P` minus the branch vertices already processed.
-/

inductive Cert where
  | node (cls : List (List Nat)) (kids : List Cert)

@[inline] def isBit (Q v : Nat) : Bool := (Q >>> v) % 2 == 1

def maskOf : List Nat → Nat
  | [] => 0
  | v :: vs => 2 ^ v ||| maskOf vs

/-- every member `v` of the class has no neighbour inside the class -/
def indepL (adj : Nat → Nat) (m : Nat) : List Nat → Bool
  | [] => true
  | v :: vs => (adj v &&& m) == 0 && indepL adj m vs

def unionL (adj : Nat → Nat) : List (List Nat) → Option Nat
  | [] => some 0
  | c :: cs =>
    let m := maskOf c
    if indepL adj m c then (unionL adj cs).map (m ||| ·) else none

/-- child problems from the branch list `B`, removing processed vertices from `P` -/
def children (adj : Nat → Nat) (k : Nat) : Nat → List Nat → Option (List (Nat × Nat))
  | _, [] => some []
  | P, v :: vs =>
    if isBit P v then (children adj k (P ^^^ 2 ^ v) vs).map ((P &&& adj v, k - 1) :: ·) else none

/-- one node: `some kids` if the colouring is valid and covers `P` -/
def step (adj : Nat → Nat) (P k : Nat) (cls : List (List Nat)) : Option (List (Nat × Nat)) :=
  if k == 0 then none else
  match unionL adj cls with
  | none => none
  | some U =>
    if U != P then none else
    if cls.length < k then some [] else
    children adj k P (cls.drop (k - 1)).flatten

mutual
def checkCert (adj : Nat → Nat) : Cert → Nat → Nat → Bool
  | .node cls kids, P, k =>
    match step adj P k cls with
    | none => false
    | some ch => checkKids adj kids ch
def checkKids (adj : Nat → Nat) : List Cert → List (Nat × Nat) → Bool
  | [], [] => true
  | c :: cs, (P, k) :: ps => checkCert adj c P k && checkKids adj cs ps
  | _, _ => false
end
