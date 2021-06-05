Definition Var  := nat.
Definition Name := nat.

Inductive Arity := Unary | Binary.
Inductive Fn : Arity -> Type :=
| pair : Fn Binary
| pfst  : Fn Unary
| psnd  : Fn Unary
| senc : Fn Binary
| sdec : Fn Binary
| pk   : Fn Unary
| aenc : Fn Binary
| adec : Fn Binary.


Inductive Term : Type :=
| var (v : Var) : Term
| nam (n : Name) : Term
| fnu (f : Fn Unary)  : Term -> Term
| fnb (f : Fn Binary) : Term * Term -> Term.


Inductive RewriteRule : Term -> Term -> Prop :=
| pf (x : Var) (y : Var) : RewriteRule (fnu pfst  (fnb pair (var x, var y)))                  (var x)
| ps (x : Var) (y : Var) : RewriteRule (fnu psnd  (fnb pair (var x, var y)))                  (var y)
| se (x : Var) (k : Var) : RewriteRule (fnb sdec (fnb senc (var x, var k), var k))           (var x)
| ae (x : Var) (k : Var) : RewriteRule (fnb adec (fnb aenc (var x, fnu pk (var k)), var k))  (var x).


Fixpoint subst (t : Term) (repl : Term) (x : Var) : Term := match t with
| var v => if Nat.eqb x v then repl else t
| nam n => t
| fnu f t1 => fnu f (subst t1 repl x)
| fnb f p => fnb f (subst (fst p) repl x, subst (snd p) repl x)
end.


(* Hash (#) is like 'apply' *)
Notation "a '#' b | x"  := (subst a b x)                   (at level 61, left associativity).


Definition rewrites (s t : Term) : Prop := exists l r (rule : RewriteRule l r) 
  (c x y : Var) 
  (st tx ty : Term),
  s = st # (l # tx|x # ty|y)|c /\
  t = st # (r # tx|x # ty|y)|c.

Notation "a ~> b"  := (rewrites a b)        (at level 60, right associativity).


Example egaencpfstpair : fnb aenc (fnu pfst (fnb pair ( nam 3, var 1)), nam 1) ~> fnb aenc (nam 3, nam 1).
Proof.
unfold rewrites.
exists _, _, (pf 101 102).
exists 103, 101, 102. 
exists (fnb aenc (var 103, nam 1)).
exists (nam 3), (var 1).
tauto.
Qed.


Reserved Notation "x '~>*' y" (at level 80).

Inductive rewrite_star (t1 t2 : Term) : Prop :=
| refl : t1 = t2  -> t1 ~>* t2
| this : t1 ~> t2 -> t1 ~>* t2
| next (t : Term) : t1 ~>* t ->  t ~>* t2 -> t1 ~>* t2
 where "x ~>* y" := (rewrite_star x y).

Reserved Notation "x '<~>' y" (at level 80).
Inductive equal_r (t1 t2 : Term) : Prop :=
| eqr : t1 ~>* t2 -> t1 <~> t2
| eql : t2 ~>* t1 -> t1 <~> t2
| eqn (t : Term) : t1 <~> t  ->  t <~> t2 -> t1 <~> t2
 where "x <~> y" := (equal_r x y).

(*
Definition equal_r t1 t2 := t1 ~>* t2 \/ t2 ~>* t1.
Notation "a <~> b" := (equal_r a b)    (at level 60, right associativity).
*)

Lemma equal_r_refl : forall t, t <~> t.
Proof. intros. apply eql. apply refl. reflexivity. Qed.
Lemma equal_r_tran : forall s t u, s <~> t -> t <~> u -> s <~> u.
Proof. intros. apply eqn with (t:=t); tauto. Qed.
Lemma equal_r_symm : forall s t, s <~> t -> t <~> s.
Proof. intros. induction H.
 - apply eql. assumption.
 - apply eqr. assumption.
 - apply eqn with (t:=t); tauto.
Qed.



(* rewrite rule on outermost, with substitutions a b resp. Works only if your vars are under 100*)
Ltac outerwith rule a b := unfold rewrites; exists _, _, (rule 101 102), 103, 101, 102, (var 103), a, b; simpl; try tauto.

Example eg_sencpair : fnu pfst (fnb pair(fnb sdec(fnb senc(var 1, nam 5), nam 5), var 2)) <~> var 1.
Proof.
apply eqr.
apply next with (t:= (fnb sdec (fnb senc (var 1, nam 5), nam 5))); apply this.
 - outerwith pf (fnb sdec (fnb senc (var 1, nam 5), nam 5)) (var 2).
 - outerwith se (var 1) (nam 5).
Qed.


Definition terminal t := forall t', t ~>* t' -> t = t'.

(*
rewrites (s t : Term) : Prop := exists l r (rule : RewriteRule l r) 
  (c x y : Var)
  (st tx ty : Term),
  s = st # ((l # tx|x) # ty|y)|c /\
  t = st # ((r # tx|x) # ty|y)|c.
*)




(*Lemma left side cant have length one in any rule: forall v, rewrites
(first lemma for var and nam)
*)

Example varisntleft : forall x y v, fnu pfst (fnb pair (var x, var y)) <> var v.
Proof. discriminate. Qed.

Example varisntleft2 : forall f p v, var v <> fnb f p.
Proof. discriminate. Qed.

Ltac lol H c v0 := 
   unfold subst in H; destruct (Nat.eqb c v0); fold subst in H;
   discriminate H; assumption;
   discriminate H;
   discriminate H;
   discriminate H.

Lemma varcantleft : forall v st l r (rule : RewriteRule l r) tx ty x y c,
var v = st # (l # tx|x # ty|y)|c-> 
var v = st.
Proof. 
intros. inversion rule;
   (subst; simpl in *; destruct (Nat.eqb x x0); try destruct (Nat.eqb x y0); try destruct (Nat.eqb x k);
   (destruct st;
   [ unfold subst in H; destruct (Nat.eqb c v0); fold subst in H; try discriminate H; try assumption
   | discriminate H | discriminate H | discriminate H])).
Qed.


Example varcantsubleft : forall v x y, var v <> fnu pfst (fnb pair (var x, var y)) .


Lemma varterminal : forall v, terminal (var v).
Proof. intros. unfold terminal; intros. inversion H.
 - assumption.
 - unfold rewrites in *. destruct H0 as [l [r [rule [c [x [y [st [tx [ty [Hs Ht]]]]]]]]]]. 
   inversion rule.
  + subst. rewrite Hs. inversion st; destruct st.
    * admit.
  + admit.
  + 


Fixpoint termlen (t : Term) : nat := match t with
| var v          => 1
| nam n          => 1
| fnu f t1       => 1 + termlen t1
| fnb f (t1, t2) => 1 + termlen t1 + termlen t2
end.

Lemma terminalone : forall t, termlen t = 1 -> terminal t.
Proof. intros.


Theorem normalizing : forall s t, s ~> t -> exists t', t ~>* t' /\ terminal t'.
Proof. induction s; intros.
 - 



