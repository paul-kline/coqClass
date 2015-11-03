


Inductive SC : Type :=
| Value : nat -> SC
| Unknown : SC.

Inductive NatStack : Type :=
| Empty : NatStack
| Add : nat -> NatStack -> NatStack.


Module problem1.

Definition push(n:nat) (ns : NatStack) : NatStack :=
   Add n ns.

Definition pop(ns : NatStack) : NatStack :=
   match ns with
    | Empty => Empty 
    | Add _ ns' => ns' 
   end.

Definition top (ns:NatStack):SC :=
   match ns with 
    | Empty => Unknown
    | Add x _ => Value x
   end. 

Definition isEmpty(ns : NatStack) : bool :=
   match ns with 
    | Empty => true
    | Add _ _ => false
   end.


(* push 

PRECONDITIONS:
      true *)(*
POSTCONDITIONS:
     1.  forall n : nat and ns : NatStack, push n ns <> Empty          
     2.  n is on top of (push n ns) forall ns.
             n = top (push n ns)

  INVARIANTS:
     1. All elements 'below' the newly pushed object remain unchanged.
         pop (push n ns) = ns *)


(* pop 

PRECONDITIONS:
      true*)(*
POSTCONDITIONS:
     1.  if ns<>Empty, then |ns| = |pop ns| + 1
     2.  top (pop (push n ns)) = n iff top ns = n 
  INVARIANTS:
     1. All elements 'below' the newly removed object remain unchanged.
         pop (push n ns) = ns 
*)


(* top 

PRECONDITIONS:
      true *)(*
POSTCONDITIONS:
     1.  top (push n ns) = Value n 

  INVARIANTS:
     1. ns is unchanged. 
*)


(* isEmpty
PRECONDITIONS:
      true*)(*
POSTCONDITIONS:
     1.  empty <==> true 
     2.  push n ns <==> false

  INVARIANTS:
     1. ns is unchanged.
*)

Fixpoint size(ns:NatStack) : nat :=
  match ns with 
    | Empty => O
    | Add _ ns' => S (size ns')
  end.

Theorem pushPOST1 : forall n :nat, forall ns:NatStack, push n ns <> Empty.
  Proof. intros. unfold push. discriminate. Qed.
Theorem pushPOST2 : forall n : nat, forall ns:NatStack, top (push n ns) = Value n.
  Proof. intros.  simpl. reflexivity. Qed.
Theorem pushINVARIANT1 : forall n :nat, forall ns : NatStack, pop (push n ns) = ns.
  Proof. intros.  simpl. reflexivity. Qed.


Theorem popPost1 : forall ns:NatStack, ns <>Empty -> size ns = S (size (pop ns)).
  Proof. intros. induction ns. elim H. reflexivity.
    simpl. reflexivity. Qed.
Theorem popPost2 : forall ns:NatStack, forall n:nat, top ns = Value n <-> Value n = top (pop (push n ns)).
 Proof.  split. simpl. intros. elim H. reflexivity. 
         simpl. symmetry. elim H. reflexivity. Qed.
Theorem popINVARIANT1: forall n : nat, forall ns : NatStack, pop (push n ns) = ns.
 Proof. apply pushINVARIANT1. Qed.

Theorem topPOST1 : forall ns:NatStack, forall n :nat, top (push n ns) = Value n .
 Proof. intros. simpl. reflexivity. Qed.
Theorem topINVARIANT1 : forall ns:NatStack, forall n : nat, (top (push n ns)) = Value n -> ns = ns.
 Proof. intros. reflexivity. Qed. 

Definition s1 := push 1 (push 2 (push 3 Empty)).
Definition emp := Empty .

Eval compute in pop ( s1).
Eval compute in pop (pop s1).
Eval compute in pop (pop (pop s1)).
Eval compute in pop (pop (pop (pop s1))).


End problem1. 


Module problem2. 

Inductive SC : Type :=
| Value : nat -> SC
| Unknown : SC.

Inductive NatStack : Type :=
| Empty : NatStack
| Add : nat -> NatStack -> NatStack.


Module problem1.

Definition push(sc:SC) (ns : NatStack) : NatStack :=
   match sc with 
    | Unknown => ns 
    | Value n => Add n ns
   end.

Definition pop(ns : NatStack) : NatStack :=
   match ns with
    | Empty => Empty 
    | Add _ ns' => ns' 
   end.

Definition top (ns:NatStack):SC :=
   match ns with 
    | Empty => Unknown
    | Add x _ => Value x
   end. 

Definition isEmpty(ns : NatStack) : bool :=
   match ns with 
    | Empty => true
    | Add _ _ => false
   end.





