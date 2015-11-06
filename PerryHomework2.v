


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

Theorem isEmptyPOST1 : forall s : NatStack, isEmpty s = true <-> s = Empty.
Proof. intros. split. induction s.  simpl. symmetry. reflexivity. 
simpl. discriminate.
intros. rewrite H.  simpl.  reflexivity. Qed. 
Theorem isEmptyPOST2 : forall s : NatStack, isEmpty s = false <-> s <> Empty.
Proof. intros. split. intros. destruct s. discriminate.
simpl. discriminate. intros. unfold isEmpty. destruct s. elim H.  reflexivity. 
reflexivity.  Qed. 
Theorem isEmptyINVARIANT1 : forall s : NatStack, isEmpty s = true /\ isEmpty s = false -> s = s.
Proof. intros.  reflexivity. Qed. 

Definition s1 := push 1 (push 2 (push 3 Empty)).
Definition emp := Empty .

Eval compute in pop ( s1).
Eval compute in pop (pop s1).
Eval compute in pop (pop (pop s1)).
Eval compute in pop (pop (pop (pop s1))).


End problem1. 


Module problem2. 

Inductive SC (T :Type): Type :=
| Value : T -> SC T
| Unknown : SC T.

Inductive Stack (T:Type) : Type :=
| Empty : Stack T
| Add : T -> Stack T -> Stack T.

Eval compute in Add nat 4 (Empty nat).


Definition push {T:Type} (t:T) (st : Stack T) : Stack T:=
   Add T t st.

Definition pop {T:Type} (s : Stack T) : Stack T :=
   match s with
    | Empty => Empty T 
    | Add _ s' => s' 
   end.

Definition top {T:Type} (s:Stack T): SC T :=
   match s with 
    | Empty => Unknown T
    | Add x _ => Value T x
   end. 

Definition isEmpty {T:Type} (s : Stack T) : bool :=
   match s with 
    | Empty => true
    | Add _ _ => false
   end.

Theorem pushPOST1 : forall (T:Type), forall t :T, forall s:Stack T, push t s <> Empty T.
  Proof. intros. unfold push. discriminate. Qed.
Theorem pushPOST2 : forall (T:Type), forall t : T, forall s: Stack T, top (push t s) = Value T t.
  Proof. intros.  simpl. reflexivity. Qed.
Theorem pushINVARIANT1 : forall (T:Type), forall t :T, forall s : Stack T, pop (push t s) = s.
  Proof. intros.  simpl. reflexivity. Qed.


Fixpoint size {T:Type} (s:Stack T) : nat :=
  match s with 
    | Empty => O
    | Add _ ns' => S (size ns')
  end.

Theorem popPost1 : forall T:Type, forall t:T, forall s: Stack T, s <>Empty T -> size s = S (size (pop s)).
  Proof. intros. induction s. elim H. reflexivity.
    simpl. reflexivity. Qed.
Theorem popPost2 : forall T:Type, forall t:T, forall s:Stack T, top s = Value T t <-> Value T t = top (pop (push t s)).
 Proof.  split. simpl. intros. elim H. reflexivity. 
         simpl. symmetry. elim H. reflexivity. Qed.
Theorem popINVARIANT1: forall T:Type, forall t : T, forall s : Stack T, pop (push t s) = s.
 Proof. apply pushINVARIANT1. Qed.

Theorem topPOST1 : forall T:Type, forall s:Stack T,  forall t :T, top (push t s) = Value T t .
 Proof. intros. simpl. reflexivity. Qed.
Theorem topINVARIANT1 : forall T:Type, forall s:Stack T, forall t : T, (top (push t s)) = Value T t -> s = s.
 Proof. intros. reflexivity. Qed.

Theorem isEmptyPOST1 : forall T : Type, 
                       forall s : Stack T, 
                       isEmpty s = true <-> s = Empty T.
Proof. intros. split. induction s.  simpl. symmetry. reflexivity. 
simpl. discriminate.
intros. rewrite H.  simpl.  reflexivity. Qed. 
Theorem isEmptyPOST2 : forall T : Type,
                       forall s : Stack T, 
                       isEmpty s = false <-> s <> Empty T.
Proof. intros. split. intros. destruct s. discriminate.
simpl. discriminate. intros. unfold isEmpty. destruct s. elim H.  reflexivity. 
reflexivity.  Qed. 
Theorem isEmptyINVARIANT1 : forall T: Type, 
                            forall s : Stack T, 
                            isEmpty s = true /\ isEmpty s = false -> s = s.
Proof. intros.  reflexivity. Qed. 
(*3*) 
Example prob2_3 : forall T:Type, forall x y : T, (pop (pop (push y (push x (Empty T))))) = Empty T.
Proof.  intros. simpl. reflexivity. Defined.
(* the two pops come after 2 pushes, so we have never "reached too far". We end up with the empty stack that was our base.*)
Example prob2_4 : forall T:Type, forall x: T, (pop (pop (push x (Empty T)))) = Empty T.
Proof.  intros. simpl. reflexivity. Defined.
(* We have defined pop such that popping the empty stack will simply result in another
   empty stack. This is not safe becase we have allowed for an implementer to call pop
   on an empty stack without conveying the information that the stack was already empty.
   Basically, if your code ever calls pop on empty, you screwed up somewhere, and right
   now our implementation is totally cool with you calling pop on empty-- I'll just give
   you another empty. *)
End problem2. 


Module problem3. 

Inductive Stack (T:Type) : Type :=
| Empty : Stack T
| Add : T -> Stack T -> Stack T.

Definition push {T:Type} (t:T) (st : Stack T) : Stack T:=
   Add T t st.

Definition pop {T:Type} (s : Stack T) (p : s <> (Empty T)) : Stack T.
Proof. destruct s as [|e s']. elim p.  reflexivity.  exact (s'). Defined.

Definition top {T:Type} (s:Stack T) (p:s <> Empty T): T.
Proof. destruct s. elim p. reflexivity. exact t. Defined.

Definition s1 := (Add nat 3 (Empty nat)).
Definition s1p : s1 <> Empty nat.
Proof. discriminate. Defined.

Eval compute in top s1 s1p.

Definition isEmpty {T:Type} (s : Stack T) : bool :=
   match s with 
    | Empty => true
    | Add _ _ => false
   end.


Theorem pushPOST1 : forall (T:Type), forall t :T, forall s:Stack T, push t s <> Empty T.
  Proof. intros. unfold push. discriminate. Qed.
Theorem pushPOST2 : forall (T:Type), forall t : T, forall s: Stack T, forall p : (push t s) <> Empty T, top (push t s) p = t .
  Proof. intros.  simpl. reflexivity. Qed.
Theorem pushINVARIANT1 : forall (T:Type), forall t :T, forall s : Stack T,forall p : (push t s) <> Empty T, pop (push t s) p= s.
  Proof. intros.  simpl. reflexivity. Qed.


Fixpoint size {T:Type} (s:Stack T) : nat :=
  match s with 
    | Empty => O
    | Add _ ns' => S (size ns')
  end.

Theorem popPost1 : forall T:Type, forall t:T, forall s: Stack T, forall p : (s) <> Empty T, size s = S (size (pop s p)).
  Proof. intros. induction s. elim p. reflexivity.
    simpl. reflexivity. Qed.
Theorem popPost2 : forall T:Type, 
                   forall t:T, 
                   forall s:Stack T,
                   forall p : (push t s) <> Empty T,
                   forall p2 : (s) <> Empty T,     
                   top s p2 = t <->  t = top (pop (push t s) p) p2.
 Proof.  split. simpl. intros. elim H. reflexivity. 
         simpl. symmetry. elim H. reflexivity. Qed.
Theorem popINVARIANT1: forall T:Type, 
                       forall t : T, 
                       forall s : Stack T, 
                       forall p : (push t s) <> Empty T,
                       pop (push t s) p = s.
 Proof. apply pushINVARIANT1. Qed.

Theorem topPOST1 : forall T:Type, 
                   forall s:Stack T,  
                   forall t :T, 
                   forall p : (push t s) <> Empty T, 
                   top (push t s) p = t .
 Proof. intros. simpl. reflexivity. Qed.

Theorem topINVARIANT1 : forall T:Type, 
                        forall s:Stack T, 
                        forall t : T, 
                        forall p : (push t s) <> Empty T,
                        (top (push t s)) p = t -> s = s.
 Proof. intros. reflexivity. Qed.

Theorem isEmptyPOST1 : forall T : Type, 
                       forall s : Stack T, 
                       isEmpty s = true <-> s = Empty T.
Proof. intros. split. induction s.  simpl. symmetry. reflexivity. 
simpl. discriminate.
intros. rewrite H.  simpl.  reflexivity. Qed. 
Theorem isEmptyPOST2 : forall T : Type,
                       forall s : Stack T, 
                       isEmpty s = false <-> s <> Empty T.
Proof. intros. split. intros. destruct s. discriminate.
simpl. discriminate. intros. unfold isEmpty. destruct s. elim H.  reflexivity. 
reflexivity.  Qed. 
Theorem isEmptyINVARIANT1 : forall T: Type, 
                            forall s : Stack T, 
                            isEmpty s = true /\ isEmpty s = false -> s = s.
Proof. intros.  reflexivity. Qed. 

Definition constructable (T:Type) (s :Stack T) : Prop := True.
 
Example neverEver : forall T:Type,
                    forall x : T,
                    forall s: Stack T,
                    forall p1 : (push x (Empty T)) <> Empty T,
                    forall p2 : pop (push x (Empty T)) p1 <> Empty T,
                    (constructable T (pop (pop (push x (Empty T)) p1) p2)) -> False.
Proof. intros. simpl in p2.  elim p2.  reflexivity. Qed.
(* The above proves that calling (pop (pop (push x (Empty T)))) is an impossible term
   to construct. Mainly, note that it needs a proof of the type of 'p2', which simplifes to 
   proving that Empty <> Empty. If you can do that, you've successfully proven False.
   To summarize, the above example shows that constructing a term of the form (pop (pop push _ empty)))
   implies False, an impossibility. *)
End problem3.
   