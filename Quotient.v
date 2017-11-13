Module Quotient.

Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zcompare.
Print Z.
Inductive Quot : Type :=
    | quot : Z -> positive -> Quot.


Definition qplus (a b: Quot) : Quot :=
    match a, b with
    | (quot na da), (quot nb db) =>
        quot (na * (Zpos db) + nb * (Zpos da)) (da * db)
        end.
        
Definition qmultply (a b: Quot) : Quot :=
    match a, b with
    | (quot na da) , (quot nb db) =>
        quot (na * nb) (da * db)
    end.

Definition qneg (a : Quot) : Quot :=
    match a with
    | (quot na da) =>
        quot (-na) da
        end.

Inductive iszero : Quot -> Prop :=
    | eq0 : forall p, iszero (quot Z0 p).

Definition qinv (a : Quot) (p : (~(iszero a))) : Quot.
    refine 
    ((match a as a' return (a = a' -> Quot) with
    | (quot na da) =>
        ((match na as na' return (na = na' -> a = _ -> Quot) with
            | Zneg na0 => fun _ => fun _ => quot (Zneg da) na0
            | Zpos na0 => fun _ => fun _ => quot (Zpos da) na0
            | Z0 => _
        end) _)
    end) _);
    intros;[
    subst na; subst a;destruct (p (eq0 da)) | auto | auto].
Defined.

Print Z.mul.

Open Scope Z_scope.

(*
Inductive Qgt : Quot -> Quot ->  Type :=
    | qgt : forall (na nb : Z) (da db : positive),
                (na * (Z.pos db)) > (nb * (Z.pos da)) ->
                Qgt (quot na da) (quot nb db).

*)
    
Print Zgt_compare.
Print Z.gtb.
Definition qgt (a b: Quot) : bool :=
    match a, b with
    | (quot na da), (quot nb db) =>
            Z.gtb (na * (Zpos db)) (nb * (Zpos da))
    end.

Definition qlt (a b: Quot) : bool :=
    qgt b a.

SearchPattern (bool -> bool).
Print negb.

Definition qge (a b: Quot) : bool :=
    negb (qlt a b).

Definition qle (a b :Quot) : bool :=
    negb (qgt a b).

Definition qcomp (a b:Quot) : Quot :=
    if (qgt a b) 
    then (quot 1 1)
    else if (qlt a b)
         then (quot (-1) 1)
         else (quot 0 1).
    
Theorem qinv_det :
    forall a p1 p2,
        qinv a p1 = qinv a p2.
    
    intros a;
    induction a.
    intros. destruct z; auto.
    destruct (p1 (eq0 _)).
Qed.


End Quotient.

