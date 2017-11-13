
Require Import Coq.Init.Datatypes.
Require Import Maps.
Require Import Coq.Strings.String.
Require Import Quotient.
Import Quotient.Quotient.
Require Import Context.
Import Context.Context.
Require Import Coq.Lists.List.
Require Import LibTactics.

Module UTLCWOSE.


    
Definition literal := string.

Definition disjoint_sum (A B : Prop) : Prop :=
    (A \/ B) /\ (A -> ~ B).

Definition ctxId := id.


(* Dynamic Typed Lambda calculus with fixpoint,
 type inference is nt so trivial*)
(*
Inductive ty : Type :=
    | TList : ty -> ty 
    | TNum : ty 
    | TBool : ty
    | TPair : ty -> ty -> ty
    | TFun : ty -> ty -> ty.
*)



Inductive tm : Type :=
    (* Predicate *)
    (*| atomp : tm -> tm *)
    | pairp : tm -> tm 
    | zerop : tm -> tm
    (* Operator*) 
    | car : tm -> tm 
    | cdr : tm -> tm 
    | cond : tm -> tm -> tm -> tm 
    | sapp : tm -> tm -> tm
    | sadd : tm -> tm -> tm 
    | smult : tm -> tm -> tm 
    | sneg : tm -> tm
    | sinverse : tm -> tm 
    | scomp : tm -> tm -> tm 
    (* Constructor *)
    | SVar : id -> tm
    | STrue : tm 
    | SFalse : tm 
    | SNum : Quot -> tm 
    (* All Quotient *)
    | SDouble : literal -> tm
    | SString : literal -> tm 
    | SPair : tm -> tm -> tm
    | SFun : id -> tm  -> tm
    | SSymbol : literal -> tm
    (* Statement *)
    | SSeq : tm -> tm -> tm
    | SLet : id -> tm -> tm -> tm
    | SFix : id -> id -> tm -> tm
    | SSys : id -> tm -> tm.

Hint Constructors tm.

Fixpoint subst (i : id) (to : tm) (org : tm) : tm :=
    match org with
    | pairp k => pairp (subst i to k)
    | zerop k => zerop (subst i to k)
    | car p => car (subst i to p)
    | cdr p => cdr (subst i to p)
    | cond j b1 b2 => cond (subst i to j) (subst i to b1) (subst i to b2)
    | sapp f x => sapp (subst i to f) (subst i to x)
    | sadd n m => sadd (subst i to n) (subst i to m)
    | smult n m => smult (subst i to n) (subst i to m)
    | sneg n => sneg (subst i to n)
    | sinverse n => sinverse (subst i to n)
    | scomp n m => scomp (subst i to n) (subst i to m)
    | SSys d x => SSys d (subst i to x)
    | SVar i' => if (eq_id_dec i i') then to else org
    | SPair p1 p2 => SPair (subst i to p1) (subst i to p2)
    | SFun x body => if (eq_id_dec i x) then org else SFun x (subst i to body)
    | SSeq b1 b2 => SSeq (subst i to b1) (subst i to b2)
    | SLet s bind body => if (eq_id_dec i s) 
                            then SLet s (subst i to bind) body
                            else SLet s (subst i to bind) (subst i to body)
    | SFix f x body => if (eq_id_dec i f)
                            then org
                            else if (eq_id_dec i x)
                                then org
                                else SFix f x (subst i to body)
    
    | _ => org
    end.

Notation " [ x := y ] k" := (subst x y k) (at level 50).
Inductive Value : tm -> Prop :=
    | vTrue : Value STrue
    | vFalse : Value SFalse
    | vNum : forall q, Value (SNum q)
    | vDouble : forall s, Value (SDouble s)
    | vString : forall s, Value (SString s)
    | vPair : forall pre post,
        Value pre ->
        Value post ->
        Value (SPair pre post)
    | vFun : forall id tm, 
        Value (SFun id tm)
    | vFix : forall idf idx tm,
        Value (SFix idf idx tm)
    | vSymbol : forall q, 
            Value (SSymbol q).

Hint Constructors Value.

Definition Env := Context.Context (type := tm).

(* I should make (Value tm)*)



Definition Output := list (id * tm).


Inductive step : (tm * Output) -> (tm * Output) -> Prop :=
    | spairp0 : forall j j' o1 o2,
                step (j ,o1) (j', o2) ->
                step ((pairp j), o1) ((pairp j'), o2)
    | spairpT : forall j pre post o1,
                Value j ->
                j = SPair pre post ->
                step ((pairp j), o1) (STrue, o1)
    | spairpF : forall j o1,
                Value j ->
                (forall pre post, j <> SPair pre post) ->
                step ((pairp j), o1) (SFalse, o1)
    | scar0 : forall j j' o1 o2,
                step (j, o1) (j' , o2) ->
                step ((car j), o1) ((car j'), o2)
    | scar1 : forall pre post o1,
                Value pre ->
                Value post ->
                step ((car (SPair pre post)), o1) (pre, o1)
    | scdr0: forall j j' o1 o2,
                step (j, o1) (j', o2) ->
                step ((cdr j), o1) ((cdr j'), o2)
    | scdr1 : forall pre post o1,
                Value pre ->
                Value post ->
                step ((cdr (SPair pre post)), o1) (post, o1)
    | scond0 : forall j j' a b o1 o2,
                step (j, o1) (j', o2) ->
                step ((cond j a b), o1) ((cond j' a b), o2)
    | scondT : forall a b o1,
                step ((cond STrue a b), o1) (a, o1)
    | scondF : forall a b o1,
                step ((cond SFalse a b), o1) (b, o1)
    | sapp0 : forall f f' x o1 o2,
                step (f, o1) (f', o2) ->
                step ((sapp f x), o1) ((sapp f' x), o2)
    | sapp1 : forall f x x' o1 o2,
                Value f ->
                step (x, o1) (x', o2) ->
                step ((sapp f x), o1) ((sapp f x'), o2)
    | sapp2 : forall id body arg o1,
                Value arg ->
                step ((sapp (SFun id body) arg), o1) (([ id := arg ] body), o1)
    | sapp3 : forall idf idx body arg o1,
                Value arg ->
                step ((sapp (SFix idf idx body) arg), o1) (([idf := (SFix idf idx body)] [idx := arg] body), o1)
    | sadd0 : forall a a' b o1 o2,
                step (a, o1) (a', o2) ->
                step ((sadd a b), o1) ((sadd a' b), o2)
    | sadd1 : forall a b b' o1 o2,
                Value a ->
                step (b, o1) (b', o2) ->
                step ((sadd a b), o1) ((sadd a b'), o2)
    | sadd2 : forall a b o1,
                step ((sadd (SNum a) (SNum b)), o1) ((SNum (qplus a b)), o1)
    
    | smult0 : forall a a' b o1 o2,
                step (a, o1) (a', o2) ->
                step ((smult a b), o1) ((smult a' b), o2)
    | smult1 : forall a b b' o1 o2,
                Value a ->
                step (b, o1) (b', o2) ->
                step ((smult a b), o1) ((smult a b'), o2)
    | smult2 : forall a b o1,
                step ((smult (SNum a) (SNum b)), o1) ((SNum (qmultply a b)), o1)
    | sneg0 : forall a a' o1 o2,
                step (a, o1) (a', o2) ->
                step ((sneg a), o1) ((sneg a'), o2)
    | sneg1 : forall a o1,
                step ((sneg (SNum a)), o1) ((SNum (qneg a)), o1)
    | sinv0 : forall a a' o1 o2,
                step (a, o1) (a', o2) ->
                step ((sinverse a), o1) ((sinverse a'), o2)
    | sinv1 : forall a o1 (p : ~iszero a),
                step ((sinverse (SNum a)), o1) ((SNum (qinv a p)), o1)
    (* If it's zero, stuck *)
    | scomp0 : forall a a' b o1 o2,
                step (a, o1) (a', o2) ->
                step ((scomp a b), o1) ((scomp a' b), o2)
    | scomp1 : forall a b b' o1 o2,
                Value a ->
                step (b, o1) (b', o2) ->
                step ((scomp a b), o1) ((scomp a b'), o2)
    | scomp2 : forall a b o1,
                step ((scomp (SNum a) (SNum b)), o1) ((SNum (qcomp a b)), o1)
    

    | ssys0 : forall d a a' o1 o2,
                    step (a, o1) (a', o2) ->
                    step (SSys d a, o1) (SSys d a', o2)
    | ssys1 : forall d a o1,
                    Value a ->
                    step (SSys d a, o1) (STrue, (d,a):: o1)
    | sseq0 : forall a a' b o1 o2,
                step (a, o1) (a', o2) ->
                step ((SSeq a b), o1) ((SSeq a' b), o2)
    | sseq1 : forall a b  o1,
                Value a ->
                step ((SSeq a b), o1) (b, o1)
    | slet0 : forall i bind bind' body o1 o2,
                step (bind, o1) (bind', o2) ->
                step ((SLet i bind body), o1) ((SLet i bind' body), o2)
    | slet1 : forall i bind body o1,
                Value bind ->
                step ((SLet i bind body), o1) (([ i := bind ] body), o1).
   
Notation "a ==> b" := (step a b) (at level 30).

Hint Constructors step.

Definition first {A B: Type} (x : A * B) : A :=
    match x with
        | (a, b) => a
    end.

Definition second {A B: Type} (x : A * B) : B :=
    match x with
        | (a, b) => b
    end.

Definition no_next (term : tm * Output) : Prop :=
    (~exists next, term ==> next).

Definition stuck ( term : tm * Output) : Prop :=
    (~ Value (first term)) \/ (no_next term).

Inductive TRC {Z : Type} (rel : Z -> Z -> Prop) : Z -> Z -> Prop :=
    | trcRefl : forall (x : Z), ((TRC rel) x x)
    | trcTrans : forall (x y z : Z), rel x y -> rel y z -> ((TRC rel) x z).

Definition multistep := TRC step.

Notation "a ==>* b" := (multistep a b) (at level 29).

Inductive machine {P O : Type} 
    (step : P*(list O) -> P*(list O) -> Prop) 
    (value : P -> Prop)
    (program : P) : P -> nat -> list O -> Prop :=
    | mO : machine step value program program 0 nil
    | mS : forall (a a' : P) (o1 o2 : list O) n,
        machine step value program a n o1 ->
        step (a, o1) (a', o2) ->
        machine step value program a' (S n) o2
    | mP : forall t' n o,
        machine step value program t' n o ->
        value t' ->
        machine step value program t' (S n) o.
(*
Definition machStep := machine step Value.

Definition intepreterCorrect (intep : nat -> tm -> Output) :=
    forall (n : nat) (t t': tm) (o : Output) 
    (mach : machStep t t' n o), 
    exists (m: nat) (t' : tm), intep m t = o.


Definition transformationCorrect (transf : tm -> tm) :=
    forall (n : nat) (t t': tm) (o : Output) (mach : machStep t t' n o),
    exists (m:nat) (t'' : tm), machStep (transf t) t' m o.
*)
Definition determinism {Z : Type} (step : Z -> Z -> Prop) :=
    forall x y1 y2, 
        step x y1 ->
        step x y2 ->
        y1 = y2.

Ltac general_val_ X u v :=
        match v with
          | 0 => X;(generalize dependent u)
          | _ => general_val_ ltac:(X; generalize dependent u) v
        end.
    
Ltac glize := general_val_ idtac.

Ltac forwardALL :=
    match goal with
     | H : ( _ -> _) |- _ => forwards* : H; generalize H; clear H; forwardALL
     | H : _ |- _ => idtac; intros
     end.


     Theorem Value_not_Steppable:
     forall x y o1 o2,
         Value x ->
         ~ (step (x, o1) (y, o2)).
 
     unfold not; intros x y o1 o2 h1;
     glize y o1 o2 0.
     induction h1; intros o2 o1 y h2; 
     inversion h2; subst.
 Qed.
 

Ltac getInfo :=
 match goal with
 | H : (_,_) = _ |- _ => inversion H; subst; (try clear H) ; getInfo
 | |- _ => idtac
 end.


Ltac contra_ValueNotSteppable :=
try (intros;subst;
    match goal with
    | H0 : (step (?X, _) _) , H1 : Value ?X |- _ =>
    (destruct (Value_not_Steppable _ _ _ _ H1 H0); fail)
    | H0 : (step (_ ?X, _) _) , H1 : Value ?X |- _ =>
        (inversion H0; subst; try (clear H0; contra_ValueNotSteppable); fail)
    | |- _ => idtac
    end
).


Ltac IntroDestructAndAuto_Step :=
try (intros;subst;
try match goal with
| H : step (_ _ ,_) _ |- _ => inversion H; subst; clear H
end; 
subst;
forwardALL; subst;
try contra_ValueNotSteppable;
try match goal with
| H : _ = _ |- _ => inversion H; subst; clear H
end;
eauto
).

Ltac cpos H :=
    pose H as HIHIHI; generalize HIHIHI; clear HIHIHI; intro.





    Ltac Strong_contra_ValueNotSteppable :=
    try (
       match goal with
       | H: step (?X, _) _ |- _ => 
       assert (Value X);  eauto; 
       contra_ValueNotSteppable ; fail
       | H: step (?P ?X, _) _ |- _ =>
           inversion H; subst; clear H; Strong_contra_ValueNotSteppable; fail
       | |- _ => idtac
       end
    ).
   

Lemma detStep0 :
    forall x y y' o1 o2 o3,
        step (x, o1) (y, o2) ->
        step (x, o1) (y', o3) ->
        y = y'.
Proof.

    intros x y y' o1 o2 o3 h1;
    glize y' o3 0. 
    remember (x, o1) as s1;
    remember (y, o2) as s2.
    glize x y o1 o2 0.
    induction h1;
    intros; getInfo;
        IntroDestructAndAuto_Step;
        Strong_contra_ValueNotSteppable.
    destruct (H6 pre post eq_refl).
    destruct (H0 pre post eq_refl).                                                  
    assert (qinv a p = qinv a p0);
    try eapply qinv_det;subst; eauto.
    rewrite H; auto.

(* It's said to be the side effect from eauto. 
    No worry.
*)
    Unshelve.
    Strong_contra_ValueNotSteppable.
    Strong_contra_ValueNotSteppable.
    auto. auto.
    Strong_contra_ValueNotSteppable.
    Strong_contra_ValueNotSteppable.
    auto. auto.
    auto. auto. 
 
Qed.
    

Lemma detStep1:
    forall x y y' o1 o2 o3,
        step (x, o1) (y, o2) ->
        step (x, o1) (y', o3) ->
            o2 = o3.

    intros x y y' o1 o2 o3 h1;
    glize y' o3 0. 
    remember (x, o1) as s1;
    remember (y, o2) as s2.
    glize x y o1 o2 0.
    induction h1;
    intros; getInfo;
    IntroDestructAndAuto_Step;
    Strong_contra_ValueNotSteppable.
    (* Again ..*)
    Unshelve. 
    Strong_contra_ValueNotSteppable.
    Strong_contra_ValueNotSteppable.
    auto. auto.
    Strong_contra_ValueNotSteppable.
    Strong_contra_ValueNotSteppable.
    auto. auto.
    auto. auto.
Qed.

Theorem step_determinsm:
    determinism step.
    unfold determinism.
    intros.
    destruct x;
    destruct y1;
    destruct y2.
    assert (t0 = t1). eapply detStep0; eauto.
    assert (o0 = o1). eapply detStep1; eauto.
    subst; auto.
Qed.


(*
    Classify Unstuck Program.
    Without typing it.
    It's the most important part;
    or I cannot do induction on 'tm'.
*)

(*
    After Consideration,
    unstuck program is hard to classify without
    the help of typing. (And I also want sthing strong as sum type)
    (At least the two branch of if can give different type)
    So I only deal with those without free variable.
    And that makes the 'value' of the 'machine' changes
    to 'stuck' (no next step).
    I hope that makes things easier.
*)

(*
    The Whole VEmeschc is to verify:
        cps transform;
        name elimination;
        backend;
    Three parts. 
    A 'closed' program is all this need to compile.
    It's actually a variation of Emeschc.
    Parser and ToC is not going to be verified.
*)

(*
    Later, proof will largely be inductions on
    a closed program.
    I need an algorithm to check a 'tm' is closed or not.
*)

Definition no_step (t : tm) :=
    forall o, no_next (t, o).

Definition machStep := machine step no_step.

Definition intepreterCorrect (intep : nat -> tm -> Output) :=
    forall (n : nat) (t t': tm) (o : Output) 
    (mach : machStep t t' n o), 
    exists (m: nat) (t' : tm), intep m t = o.


Definition transformationCorrect (transf : tm -> tm) :=
    forall (n : nat) (t t': tm) (o : Output) (mach : machStep t t' n o),
    exists (m:nat) (t'' : tm), machStep (transf t) t' m o.

Inductive free : id -> tm -> Prop :=
    | fpairp : forall i x,
                free i x ->
                free i (pairp x)
    | fzerop : forall i x,
                free i x ->
                free i (zerop x)
    | fcar : forall i x,
                free i x ->
                free i (car x)
    | fcdr : forall i x,
                free i x ->
                free i (cdr x)
    | fcond0 : forall i x y z,
                free i x ->
                free i (cond x y z)
    | fcond1 : forall i x y z,
                free i y ->
                free i (cond x y z)
    | fcond2 : forall i x y z,
                free i z ->
                free i (cond x y z)
    | fapp0 : forall i x y,
                free i x ->
                free i (sapp x y)
    | fapp1 : forall i x y,
                free i y ->
                free i (sapp x y)
    | fadd0 : forall i x y,
                free i x ->
                free i (sadd x y)
    | fadd1 : forall i x y,
                free i y ->
                free i (sadd x y)
    | fmult0 : forall i x y,
                free i x ->
                free i (smult x y)
    | fmult1 : forall i x y,
                free i y ->
                free i (smult x y)
    | fneg : forall i x,
                free i x ->
                free i (sneg x)
    | finv : forall i x,
                free i x ->
                free i (sinverse x)
    | fcomp0 : forall i x y,
                free i x ->
                free i (scomp x y)
    | fcomp1 : forall i x y,
                free i y ->
                free i (scomp x y)
    | fvar : forall i,
                free i (SVar i)
    | fpair0 : forall i x y,
                free i x ->
                free i (SPair x y)
    | fpair1 : forall i x y,
                free i y ->
                free i (SPair x y)
    | ffun : forall i j x,
                free i x ->
                i <> j ->
                free i (SFun j x)
    | fseq0 : forall i x y,
                free i x ->
                free i (SSeq x y)
    | fseq1 : forall i x y,
                free i y ->
                free i (SSeq x y)
    | flet0: forall i j x y,
                free i x ->
                free i (SLet j x y)
    | flet1 : forall i j x y,
                free i y ->
                i <> j ->
                free i (SLet j x y)
    | ffix : forall i f v body,
                free i body ->
                i <> f ->
                i <> v ->
                free i (SFix f v body)
    | fsys : forall i j e,
                free i e ->
                free i (SSys j e).


Inductive closed : tm -> Prop :=
    | cpairp : forall x,
                closed x ->
                closed (pairp x)
    | czerop : forall x,
                closed x ->
                closed (zerop x)
    | ccar: forall x,
                closed x ->
                closed (car x)
    | ccdr: forall x,
                closed x ->
                closed (cdr x)
    | ccond : forall x y z,
                closed x ->
                closed y ->
                closed z ->
                closed (cond x y z)
    | capp : forall x y,
                closed x ->
                closed y ->
                closed (sapp x y)
    | cadd : forall x y,
                closed x ->
                closed y ->
                closed (sadd x y)
    | cmult : forall x y,
                closed x ->
                closed y ->
                closed (smult x y)
    | cneg : forall x,
                closed x ->
                closed (sneg x)
    | cinverse : forall x,
                closed x ->
                closed (sinverse x)
    | ccomp : forall x y,
                closed x ->
                closed y ->
                closed (scomp x y)
    | ctrue : closed (STrue)
    | cfalse : closed (SFalse)
    | cnum : forall n, closed (SNum n)
    | cdouble : forall n, closed (SDouble n)
    | cstring : forall s, closed (SString s)
    | cpair : forall x y,
                closed x ->
                closed y ->
                closed (SPair x y)
    | cfun : forall i body,
                closed ([i := STrue] body) ->
                closed (SFun i body)
    | csymbol : forall s, closed (SSymbol s)
    | cseq : forall a b,
                closed a ->
                closed b ->
                closed (SSeq a b)
    | clet : forall i bind body,
                closed bind ->
                closed ([i := STrue] body) ->
                closed (SLet i bind body)
    | cfix : forall i j body,
                closed ([i := STrue] [j := STrue] body) ->
                closed (SFix i j body)
    | csys : forall i e,
                closed e ->
                closed (SSys i e).

Hint Constructors free.
Hint Constructors closed.

Ltac contra_free_unfree :=
try (
    intros; 
    match goal with
    | H0 : ~ (?X) , H1 : ?X |- _ => destruct (H0 H1)
    end
).

Ltac IntroDestructAndAuto_free :=
try (intros;subst;
try match goal with
| H : (free _ (_ _)) |- _ => inversion H; subst; clear H
end; 
subst;
forwardALL; subst;
try contra_free_unfree;
try match goal with
| H : _ = _ |- _ => inversion H; subst; clear H
end;
eauto
).

Ltac contra_inversionUnfree :=
try (intros; subst;
try match goal with
| H: (free _ _) |- _ => inversion H; subst; clear H; contra_inversionUnfree
| |- _ => idtac
end
).


Lemma subst_keep_free :
    forall i j x,
        free i x ->
        i <> j ->
        free i ([j := STrue] x).
intros i j x h;
glize j 0.
induction h; intros; subst; cbn; eauto.
(* Case SVar *)
rewrite eq_id_dec_dif1; eauto.
destruct (eq_id_dec j0 j); eauto.
destruct (eq_id_dec j0 j); eauto.
destruct (eq_id_dec j0 j); eauto.
destruct (eq_id_dec j f); eauto.
destruct (eq_id_dec j v); eauto.
Qed.
(*
Ltac rewrite_right_to_left_in_subst_dupli :=
match goal with
| H : forall _, ( _ = _ )|- _ => idtac H; repeat erewrite <- H; clear H; rewrite_right_to_left_in_subst_dupli
| |- _ => idtac 0
end.


Lemma weak_subst_dupli:
    forall i x,
        [i := STrue] x = [i := STrue] ([i := STrue] x).

intros i x; glize i 0;
induction x; intros; subst; cbn; eauto;
rewrite_right_to_left_in_subst_dupli; eauto.
destruct (eq_id_dec i0 i); eauto.
compute. rewrite eq_id_dec_dif0; eauto.
destruct (eq_id_dec i0 i); eauto.
Abort.


*)


Lemma closed_imply_nofree :
    forall t,
        closed t -> (forall i, ~free i t).
    
intros t h;
induction h; intros;intro;
IntroDestructAndAuto_free.
contra_inversionUnfree.
contra_inversionUnfree.
assert (free i0 ([i := STrue] body)) as HHH.
eapply subst_keep_free; eauto.
destruct (IHh _ HHH).
assert (free i0 ([i := STrue] body)) as HHH.
eapply subst_keep_free; eauto.
destruct (IHh2 _ HHH).
assert (free i0 ([i := STrue] [j:= STrue] body)).
assert (free i0 ([j := STrue] body)).
eapply subst_keep_free; eauto.
eapply subst_keep_free; eauto.
destruct (IHh _ H0).
Unshelve.
auto. auto. auto. auto.
auto. auto. auto. auto.
auto. auto. auto. auto.
auto.
Qed.

Ltac destructALL :=
    match goal with
    | H : {_} + {_} |- _ => destruct H; destructALL
    | |- _ => idtac
    end.

Ltac IntroDestructAndAuto_closed :=
    try (intros;subst;
    try match goal with
    | H : (closed (_ _)) |- _ => inversion H; subst; clear H
    end; 
    subst;
    forwardALL; subst;
    try contra_free_unfree;
    try match goal with
    | H : _ = _ |- _ => inversion H; subst; clear H
    end;
    eauto
    ).

Ltac byGuess_closed_dec :=
    match goal with
    | H : ~ closed _ |- _ => right; intro; IntroDestructAndAuto_closed;fail
    | H : closed _ |- _ => left; eauto;fail
    | |- _ => try (left; eauto; fail);
                try (right; intro;IntroDestructAndAuto_closed; fail); idtac
    end.

(*
    Now I really want to prove a thm:
        {closed x} + {exists i, free i x}.
    
    My idea is to prove 
        {closed x} + {~ closed x} first;
    then prove 
     ~ closed x -> exists i, free i x.
    
*)



Fixpoint check_closed (l : Context) (t : tm) : bool :=
    match t with
    | pairp a => check_closed l a
    | zerop a => check_closed l a 
    | car a => check_closed l a   
    | cdr a => check_closed l a 
    | cond a b c => andb (check_closed l a)
                        (andb (check_closed l b)
                            (check_closed l c))
    | sapp a b => andb (check_closed l a) (check_closed l b)
    | sadd a b => andb (check_closed l a) (check_closed l b)
    | smult a b =>andb (check_closed l a) (check_closed l b)
    | sneg a => check_closed l a
    | sinverse a => check_closed l a
    | scomp a b => andb (check_closed l a) (check_closed l b)
    | SVar i => byContextb l i
    | STrue => true
    | SFalse => true 
    | SNum a => true 
    | SDouble a => true 
    | SString a => true 
    | SPair a b => andb (check_closed l a) (check_closed l b)
    | SFun i b => check_closed (update i 0 l) b
    | SSymbol a => true 
    | SSeq a b => andb (check_closed l a) (check_closed l b)
    | SLet i bind body => andb (check_closed l bind) (check_closed (update i 0 l) body)
    | SFix f x body => check_closed (update f 0 (update x 0 l)) (body)
    | SSys _ e => check_closed l e
    end.

Definition checkclosed := check_closed empty.

Lemma andb_keep_true :
    forall a b,
        andb a b = true ->
        a = true /\ b = true.
    destruct a; destruct b; eauto.
Qed.

Ltac destructALLANDB :=
    match goal with
    | H : andb _ _ = true |- _ => destruct (andb_keep_true _ _ H); 
                                clear H; destructALLANDB
    | |- _ => idtac
    end.

Lemma andb_keep_true0:
    forall a b,
        a = true ->
        b = true ->
        andb a b = true.
    intros;subst; compute; auto.
Qed.

Ltac destructALLANDBINGOAL :=
match goal with
| |- andb _ _ = true => 
    repeat apply andb_keep_true0
| |- _ => idtac
end.

    
Lemma check_closed_subst_equ:
    forall i t l,
        check_closed (update i 0 l) t = true ->
        check_closed l ([i := STrue] t) = true.
    intros i t; glize i 0;
    induction t; intros; 
    try (cbn in *;destructALLANDB;forwardALL; eauto; fail);
    try (cbn in *; destructALLANDB; forwardALL;
    destructALLANDBINGOAL; eauto; fail).
    (* Case SVar *)
    cbn in *.
    destruct (eq_id_dec i i0); subst; eauto.
    rewrite eq_id_dec_id; eauto.
    cbv in H. 
    rewrite eq_id_dec_dif0; eauto.
    rewrite eq_id_dec_dif1 in H; eauto.
    (* Case SFun *)
    cbn [check_closed] in *. 
    cbn [subst]. destruct (eq_id_dec i0 i); subst; eauto.
    cbn [check_closed].
    assert (update i 0 (update i 0 l) = update i 0 l).
    apply ctxeq_ext. eapply eqShadow. eapply CtxeqId.
    rewrite <- H0. auto.
    cbn [check_closed]. 
    assert (update i0 0 (update i 0 l) = update i 0 (update i0 0 l)).
    apply ctxeq_ext. eapply eqPermute. eapply CtxeqId. auto.
    rewrite <- H0 in H. forwardALL.
    (* Case SLet *)
    cbn in *;destructALLANDB;forwardALL.
    destruct (eq_id_dec i0 i); subst; eauto;
    cbn [check_closed]; destructALLANDBINGOAL; eauto.
    assert (update i 0 (update i 0 l) = update i 0 l).
    apply ctxeq_ext. eapply eqShadow. eapply CtxeqId.
    rewrite H3 in H1. auto.
    assert (update i0 0 (update i 0 l) = update i 0 (update i0 0 l)).
    apply ctxeq_ext. eapply eqPermute. eapply CtxeqId. auto.
    rewrite <- H3 in H1. forwardALL.
    (* Case SFix *)

    cbn in *. destruct (eq_id_dec i1 i); destruct (eq_id_dec i1 i0);
    subst; eauto; cbn in *.
    assert (update i0 0 (update i0 0 (update i0 0 l)) = update i0 0 (update i0 0 l)).
    apply ctxeq_ext. eapply eqShadow. eapply CtxeqId.
    rewrite H0 in H. auto.
    assert (update i 0 (update i0 0 (update i 0 l)) = update i 0 (update i0 0 l)).
        apply ctxeq_ext. eapply eqTrans. eapply eqPermute.
        eapply CtxeqId. auto. eapply eqSymm. eapply eqTrans.
        eapply eqPermute. eapply CtxeqId. auto.
        eapply eqUpdate. eapply eqSymm. eapply eqShadow.
        eapply CtxeqId. rewrite H0 in H; auto.
    assert (update i 0 (update i0 0 (update i0 0 l)) = update i 0 (update i0 0 l)).
        apply ctxeq_ext. eapply eqUpdate. eapply eqShadow. eapply CtxeqId.
        rewrite H0 in H; auto.
    assert (update i 0 (update i0 0 (update i1 0 l)) = update i1 0 (update i 0 (update i0 0 l))).
        apply ctxeq_ext. eapply eqTrans. eapply eqUpdate.
        eapply eqPermute; auto. eapply CtxeqId. eapply eqPermute; auto.
        eapply CtxeqId. rewrite H0 in H; forwardALL; auto.

Qed.




Ltac destructALL_in_Weak_freedec k :=
    match goal with
    | H : forall _, {_} + {_} |- _ => destruct (H k); clear H; destructALL_in_Weak_freedec k
    | |- _ => idtac
    end.

Ltac byGuess_free :=
    match goal with
    | H : free _ _ |- _ => left; eauto
    | H : ~ (free _ _)  |- _=> right; intro;
        match goal with
        | H : free _ _ |- _ => inversion H; subst; eauto; try contra_free_unfree
        end
    | |- _ => try (left; eauto; fail);
              try (right; intro;
              match goal with
              | H : free _ _ |- _ => inversion H; subst; eauto; try contra_free_unfree
              end; fail); idtac
    end.

Lemma weak_free_dec :
    forall i t,
        {free i t} + {~ free i t}.

    intros i t; glize i 0.
    induction t; 
    try (intros j; destructALL_in_Weak_freedec j;
    byGuess_free; fail).
    (* Case SVar*)
    
    intros. destruct (eq_id_dec i0 i); subst; eauto.
    right; intro; byGuess_free. inversion H; subst; eauto.
    (* Case SFun*)
    intros j; destructALL_in_Weak_freedec j; try (byGuess_free; fail).
    destruct (eq_id_dec j i); subst; eauto.
    right; intro. inversion H; subst; eauto.

    (* Case SLet *)

    intros j; destructALL_in_Weak_freedec j; try (byGuess_free; fail).
    destruct (eq_id_dec j i); subst; eauto. right; intro. inversion H; subst; eauto.

    (* Case SFix *)
    intros j; destructALL_in_Weak_freedec j; try (byGuess_free; fail).
    destruct (eq_id_dec j i); destruct (eq_id_dec j i0); subst; eauto;try (byGuess_free; fail).
    right; intro. inversion H; subst; eauto.
    right; intro. inversion H; subst; eauto.
    right; intro. inversion H; subst; eauto.
Qed.


Lemma closed_alg_valid0 :
forall t,
    checkclosed t = true -> 
    closed t.

induction t; intros; 
try (cbn in *; eauto;destructALLANDB; cbn in *; eauto;fail).
cbn in *.
inversion H.
eapply cfun. 
Abort.


Inductive rel_closed : Context (type:= nat) -> tm -> Prop :=
    | rcpairp : forall C t,
                rel_closed C t ->
                rel_closed C (pairp t)
    | rczerop : forall C t,
                rel_closed C t ->
                rel_closed C (zerop t)
    | rccar : forall C t,
                rel_closed C t ->
                rel_closed C (car t)
    | rccdr : forall C t,
                rel_closed C t ->
                rel_closed C (cdr t)
    | rccond : forall C x y z,
                rel_closed C x ->
                rel_closed C y ->
                rel_closed C z ->
                rel_closed C (cond x y z)
    | rcapp : forall C x y,
                rel_closed C x ->
                rel_closed C y ->
                rel_closed C (sapp x y)
    | rcadd : forall C x y,
                rel_closed C x ->
                rel_closed C y ->
                rel_closed C (sadd x y)
    | rcmult : forall C x y,
                rel_closed C x ->
                rel_closed C y ->
                rel_closed C (smult x y)
    | rcneg : forall C x,
                rel_closed C x ->
                rel_closed C (sneg x)
    | rcinv : forall C x,
                rel_closed C x ->
                rel_closed C (sinverse x)
    | rccomp : forall C x y,
                rel_closed C x ->
                rel_closed C y ->
                rel_closed C (scomp x y)
    | rcvar : forall C x,
                byContextb C x = true ->
                rel_closed C (SVar x)
    | rctrue : forall C,
                rel_closed C STrue
    | rcfalse : forall C,
                rel_closed C SFalse
    | rcnum : forall C n,
                rel_closed C (SNum n)
    | rcdouble : forall C n,
                rel_closed C (SDouble n)
    | rcstring : forall C s,
                rel_closed C (SString s)
    | rcpair : forall C x y,
                rel_closed C x ->
                rel_closed C y ->
                rel_closed C (SPair x y)
    | rcfun : forall C i x,
                rel_closed (update i 0 C) x ->
                rel_closed C (SFun i x)
    | rcsymbol : forall C i,
                rel_closed C (SSymbol i)
    | rcseq : forall C x y,
                rel_closed C x ->
                rel_closed C y ->
                rel_closed C (SSeq x y)
    | rclet : forall C i bind body,
                rel_closed C bind ->
                rel_closed (update i 0 C) body ->
                rel_closed C (SLet i bind body)
    | rcfix : forall C f x body,
                rel_closed (update f 0 (update x 0 C)) body ->
                rel_closed C (SFix f x body)
    | rcsys : forall C i e,
                rel_closed C e ->
                rel_closed C (SSys i e).

Hint Constructors rel_closed.

Lemma inductionalize_of_check_closed0 :
    forall C x,
        check_closed C x = true ->
        rel_closed C x.

    intros C x; glize C 0.
    induction x; cbn in *; intros; try destructALLANDB;  eauto.
   Unshelve.


Qed.

Lemma andb_false_or :
    forall x y,
        andb x y = false ->
        x = false \/ y = false.
    intros x y;
    destruct x; destruct y; subst; eauto.
Qed.

Ltac destructALLANDBFalse  :=
    match goal with
    | H: andb _ _ = false |- _ => 
        destruct (andb_false_or _ _ H); clear H; destructALLANDBFalse
    | |- _ => idtac
    end.

Lemma inductionalize_of_check_closed1:
    forall C x,
        check_closed C x = false ->
        ~ (rel_closed C x).
    
    intros C x h1; intro.
    glize h1 0.
    induction H; intros hhh; 
    try (inversion hhh; subst; try destructALLANDBFalse; eauto;fail).
    (* Case SVar*)
    cbn in *. rewrite hhh in H; inversion H.
Qed.

Definition rclosed := rel_closed empty.


Theorem rel_closed_dec:
    forall C x,
        {rel_closed C x} + {~rel_closed C x}.
    
    intros C x.
    destruct (check_closed C x) eqn: h.
    left; apply inductionalize_of_check_closed0; auto.
    right; apply inductionalize_of_check_closed1; auto.
Qed.

Theorem rclosed_dec:
    forall x,
        {rclosed x} + {~rclosed x}.
    
    unfold rclosed.
    apply rel_closed_dec.
Qed.

Hint Resolve rel_closed_dec rclosed_dec contrapositive.

Ltac destruct_exists :=
    match goal with
    | H0 : exists _, _ |- _ =>
        destruct H0; destruct_exists
    | |- _ => idtac
    end.



Ltac not_r_closed_use_induction :=
    match goal with
    | H0 : ~ rel_closed ?A (?B1 ?B2) ,
        H1 : ~ rel_closed ?C ?D -> ?E |- _=>
        idtac H0;
        assert (~rel_closed A (B1 B2) -> ~rel_closed C D); [eauto 4; fail | idtac];
        assert (E); [eauto; fail | idtac]; eauto; clear H1 ;eauto; destruct_exists; eauto ;fail
    | |- _ => idtac
    end.



Lemma not_rclosed_means_has_free:
    forall x,
        ~rclosed x ->
        exists i, free i x.
    unfold rclosed;
    intros x;
    assert (forall (x: tm) (B: Prop), (rel_closed empty x -> B) -> (~B -> ~rel_closed empty x)).
    intros.
    eapply contrapositive.
Abort.

End UTLCWOSE.

(*
    Now I need several tools:
        1. WOC : Context -> Prop
            WellOrderedContext
        2. Every context can have a well ordered
            form. (A lemma)
        
        4. I have to modify the definition of rel_closed,
            especially the part
                cvar into:
                cvar : forall i,
                        rel_closed (update i 0 empty) (SVar i)
        5. After modification of the definition,
            I can prove a thm:
                forall C i x,
                    rel_closed (update i 0 C) x ->
                    free i x.
        3. forall term,
            exists C : Context,
                rel_closed C term. (A lemma)
        Then I can prove:
            ~rclosed t -> exists i, free i t. 
        And With help of 1 and 2,
             I may can achieve the fact that
                'rel_closed' is decidable,
                in which case, 
                    check_closed C x = true ->
                    rel_closed C x
                and 
                    check_closed C x = false ->
                    ~ rel_closed C x
                are what matter.
        Or maybe the check_closed cannot help me at all.
        since the definition of the rel_closed changes.
        Maybe I have to prove {rel_closed C x} + {~rel_closed C x} directly.


*)
