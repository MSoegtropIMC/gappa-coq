Add LoadPath "/usr/src/coq/Float".
Require Export AllFloat.

Section F_rnd.

Definition radix := 2%Z.

Definition radixMoreThanOne := TwoMoreThanOne.
Lemma radixNotZero: (0 < radix)%Z.
auto with zarith.
Qed.

Variable precision : nat.
Hypothesis precisionMoreThanOne : lt (1) precision.
Lemma precisionNotZero : ~(precision = (0)).
auto with zarith.
Qed.

Variable bExp : nat.
Definition bNum := iter_nat precision positive xO xH.
Definition bound := Bound bNum bExp.

Lemma pGivesBound : Zpos (vNum bound) = Zpower_nat radix precision.
unfold vNum, bound, bNum, Zpower_nat.
elim precision. trivial.
intros n H.
Opaque Zmult.
simpl.
rewrite <- H.
Transparent Zmult.
simpl.
apply refl_equal.
Qed.

Coercion Local float2R := FtoR radix.

Definition is_even (n : N) : bool :=
 match n with
 | N0 => true
 | Npos p =>
  match p with
  | xO _ => true
  | _ => false
  end
 end.

Fixpoint digit2 (p : positive) : nat :=
 match p with
 | xH => 1
 | xO p1 => S (digit2 p1)
 | xI p1 => S (digit2 p1)
 end.

Definition digit2_N (n : N) : nat :=
 match n with
 | N0 => 0
 | Npos p => digit2 p
 end.

Lemma digit2_N_0 :
 forall n : N,
 digit2_N n = 0 -> n = N0.
intro n.
unfold digit2_N, digit2.
destruct n.
trivial.
destruct p ; intro ; discriminate H.
Qed.

Lemma digit2_N_S :
 forall n : N, forall n0 : nat,
 digit2_N n = S n0 -> exists p, n = Npos p.
intros n n0.
unfold digit2_N.
destruct n.
intro H. discriminate H.
intro.
exists p.
trivial.
Qed.

Definition Ndiv2 (n : N) : N :=
 match n with
 | N0 => N0
 | Npos n1 =>
  match n1 with
  | xH => N0
  | xO n2 => Npos n2
  | xI n2 => Npos n2
  end
 end.

Lemma Ndiv2_mul2 :
 forall n : N,
 n = Ndouble (Ndiv2 n) \/ n = Ndouble_plus_one (Ndiv2 n).
intro n.
destruct n.
left. trivial.
destruct p ; [ right | left | right ] ; trivial.
Qed.

Record rnd_record : Set := rnd_record_mk {
  rnd_m : N ;
  rnd_e : Z ;
  rnd_g : bool ;
  rnd_s : bool
}.

Definition shr_aux (p : rnd_record) : rnd_record :=
 let s := rnd_g p || rnd_s p in
 let e := Zsucc (rnd_e p) in
 match (rnd_m p) with
 | N0 => rnd_record_mk N0 e false s
 | Npos m1 =>
  match m1 with
  | xH => rnd_record_mk N0 e true s
  | xO m2 => rnd_record_mk (Npos m2) e false s
  | xI m2 => rnd_record_mk (Npos m2) e true s
  end
 end.

Lemma shr_aux_mantissa :
 forall p : rnd_record,
 rnd_m (shr_aux p) = Ndiv2 (rnd_m p).
intro p.
unfold shr_aux, Ndiv2.
destruct (rnd_m p) ; try destruct p0 ; trivial.
Qed.

Lemma shr_aux_mantissa_digit :
 forall p : rnd_record,
 digit2_N (rnd_m (shr_aux p)) = pred (digit2_N (rnd_m p)).
intro p.
CaseEq (digit2_N (rnd_m p)) ; intros ; unfold shr_aux.
rewrite (digit2_N_0 _ H).
trivial.
generalize (digit2_N_S _ _ H).
rewrite <- H.
intro H0. elim H0. clear H H0. intros p0 H.
rewrite H.
destruct p0 ; trivial.
Qed.

Lemma shr_aux_exp :
 forall p : rnd_record,
 rnd_e (shr_aux p) = Zsucc (rnd_e p).
intro p.
unfold shr_aux.
destruct (rnd_m p) ; try destruct p0 ; trivial.
Qed.

Lemma shr_aux_guard :
 forall p : rnd_record,
 rnd_g (shr_aux p) = negb (is_even (rnd_m p)).
intro p.
unfold shr_aux, is_even.
destruct (rnd_m p) ; try destruct p0 ; trivial.
Qed.

Lemma shr_aux_sticky :
 forall p : rnd_record,
 rnd_s (shr_aux p) = rnd_g p || rnd_s p.
intro p.
unfold shr_aux.
destruct (rnd_m p) ; try destruct p0 ; trivial.
Qed.

Definition bracket (r : R) (p : rnd_record) :=
 let m := (Z_of_N (rnd_m p) * 2)%Z in
 let e := (rnd_e p - 1)%Z in
 let f0 := Float m e in
 let f1 := Float (m + 1)%Z e in
 let f2 := Float (m + 2)%Z e in
 if (rnd_g p) then
  if (rnd_s p) then (f1 < r < f2)%R else (r = f1)%R
 else
  if (rnd_s p) then (f0 < r < f1)%R else (r = f0)%R.

Lemma Rlt_Float_exp :
 forall m1 m2 : Z, forall e : Z,
 (m1 < m2)%Z -> (Float m1 e < Float m2 e)%R.
intros m1 m2 e H.
unfold float2R, FtoR.
apply Rlt_monotony_exp with (1 := radixMoreThanOne).
apply Rlt_IZR.
exact H.
Qed.

Lemma Rle_Float_exp :
 forall m1 m2 : Z, forall e : Z,
 (m1 <= m2)%Z -> (Float m1 e <= Float m2 e)%R.
intros m1 m2 e H.
unfold float2R, FtoR.
apply Rle_monotone_exp with (1 := radixMoreThanOne).
apply Rle_IZR.
exact H.
Qed.

Lemma Req_Float_exp :
 forall m1 m2 : Z, forall e : Z,
 (m1 = m2)%Z -> float2R (Float m1 e) = float2R (Float m2 e).
intros m1 m2 e H.
unfold float2R, FtoR.
simpl.
ring.
apply Rmult_eq_compat_l.
apply IZR_eq.
exact H.
Qed.

Lemma shift_float :
 forall m e : Z,
 float2R (Float m e) = float2R (Float (m * 2) (e - 1)).
intros m e.
unfold float2R, FtoR.
simpl.
rewrite mult_IZR.
replace (IZR (Zpos 2)) with 2%R.
2: trivial.
unfold Zminus.
assert (2 <> 0)%R.
auto with real.
rewrite powerRZ_add with (1 := H).
rewrite powerRZ_Zopp with (1 := H).
rewrite powerRZ_1.
field.
exact H.
Qed.

Lemma Ndiv2_even :
 forall n : N,
 is_even n = true -> (Z_of_N (Ndiv2 n) * 2)%Z = (Z_of_N n)%Z.
unfold is_even, Ndiv2.
intros n H.
destruct n ; try destruct p ; try discriminate H.
trivial.
rewrite Zmult_comm.
trivial.
Qed.

Lemma Ndiv2_odd :
 forall n : N,
 is_even n = false -> (Z_of_N (Ndiv2 n) * 2)%Z = (Z_of_N n - 1)%Z.
unfold is_even, Ndiv2.
intros n H.
destruct n ; try destruct p ; try discriminate H.
2: trivial.
rewrite Zmult_comm.
trivial.
Qed.

Lemma shr_bracket :
 forall r : R, forall p : rnd_record,
 bracket r p -> bracket r (shr_aux p).
intros r p H.
unfold bracket.
rewrite (shr_aux_guard p).
rewrite (shr_aux_sticky p).
rewrite (shr_aux_mantissa p).
rewrite (shr_aux_exp p).
replace (Zsucc (rnd_e p) - 1)%Z with (rnd_e p).
2: auto with zarith.
CaseEq (is_even (rnd_m p)) ; intro H0 ;
 [ rewrite Ndiv2_even with (1 := H0) | rewrite Ndiv2_odd with (1 := H0) ] ;
 CaseEq (rnd_g p) ; intro H1 ; simpl.
unfold bracket in H. rewrite H1 in H.
clear H1.
assert (Float (Z_of_N (rnd_m p) * 2 + 1) (rnd_e p - 1) <= r < Float (Z_of_N (rnd_m p) * 2 + 2) (rnd_e p - 1))%R.
destruct (rnd_s p).
split.
apply Rlt_le with (1 := proj1 H).
exact (proj2 H).
split.
apply Req_le with (1 := (sym_eq H)).
rewrite H.
apply Rlt_Float_exp.
auto with zarith.
clear H.
split ; rewrite shift_float.
apply Rlt_le_trans with (2 := proj1 H1). clear H1.
apply Rlt_Float_exp.
auto with zarith.
apply Rlt_le_trans with (1 := proj2 H1). clear H1.
apply Rle_Float_exp.
auto with zarith.
CaseEq (rnd_s p) ; intro H2.
unfold bracket in H. rewrite H1 in H. rewrite H2 in H.
split ; rewrite shift_float.
apply Rle_lt_trans with (2 := proj1 H). clear H.
apply Rle_Float_exp.
auto with zarith.
apply Rlt_le_trans with (1 := proj2 H). clear H1.
apply Rle_Float_exp.
auto with zarith.
unfold bracket in H. rewrite H1 in H. rewrite H2 in H.
rewrite shift_float.
rewrite H.
apply Req_Float_exp.
apply refl_equal.
unfold bracket in H. rewrite H1 in H.
clear H1.
assert (Float (Z_of_N (rnd_m p) * 2 + 1) (rnd_e p - 1) <= r < Float (Z_of_N (rnd_m p) * 2 + 2) (rnd_e p - 1))%R.
destruct (rnd_s p).
split.
apply Rlt_le with (1 := proj1 H).
exact (proj2 H).
split.
apply Req_le with (1 := (sym_eq H)).
rewrite H.
apply Rlt_Float_exp.
auto with zarith.
clear H.
split ; rewrite shift_float.
apply Rlt_le_trans with (2 := proj1 H1). clear H1.
apply Rlt_Float_exp.
auto with zarith.
apply Rlt_le_trans with (1 := proj2 H1). clear H1.
apply Rle_Float_exp.
auto with zarith.
CaseEq (rnd_s p) ; intro H2.
unfold bracket in H. rewrite H1 in H. rewrite H2 in H.
split ; rewrite shift_float.
apply Rle_lt_trans with (2 := proj1 H). clear H.
apply Rle_Float_exp.
auto with zarith.
apply Rlt_le_trans with (1 := proj2 H). clear H1.
apply Rle_Float_exp.
auto with zarith.
unfold bracket in H. rewrite H1 in H. rewrite H2 in H.
rewrite shift_float.
rewrite H.
apply Req_Float_exp.
ring.
Qed.

Fixpoint shr (p : rnd_record) (n : nat) { struct n } : rnd_record :=
 match n with
 | O => p
 | S n1 => shr (shr_aux p) n1
 end.

Fixpoint shl_aux (p : positive) (n : nat) { struct n } : positive :=
 match n with
 | O => p
 | S p1 => shl_aux (xO p) p1
 end.

Definition shl (m : positive) (e : Z) (n : nat) : rnd_record :=
 rnd_record_mk (Npos (shl_aux m n)) (e - n) false false.

Definition rnd_aux (m : positive) (e : Z) : rnd_record :=
 let n := digit2 m in
 let r :=
  if le_lt_dec n precision then
   shl m e (precision - n)
  else
   shr (rnd_record_mk (Npos m) e false false) (n - precision)
  in
 if Zle_bool (-bExp) (rnd_e r) then r
 else shr r (Zabs_nat (bExp + (rnd_e r))).

(* r.m est non nul puisque le shr n'a lieu que si n >
   prec donc il reste des bits. r.m a exactement prec
   bits. res.m a au plus prec bits, et res.e vaut au
   moins -bExp. S'il y a eu un décalage, res.e vaut
   -bExp. res.m n'est différent de r.m que s'il y a
   eu décalage, cad si res.e vaut -bExp. De meme,
   res.m n'a moins de prec bits que si res.e vaut -bExp. *)

Axiom rnd_bracket :
 forall m : positive, forall e : Z,
 bracket (Float (Zpos m) e) (rnd_aux m e).

Axiom rnd_exp_zero :
 forall m : positive, forall e : Z,
 let r := rnd_aux m e in
 rnd_m r = N0 -> (rnd_e r = -bExp)%Z.

Definition rndZ_fun (r : rnd_record) : bool := false.

Definition rndU_fun (r : rnd_record) : bool :=
 rnd_g r || rnd_s r.

Definition rndO_fun (r : rnd_record) : bool :=
 (rnd_g r || rnd_s r) && is_even (rnd_m r).

Definition rndCE_fun (r : rnd_record) : bool :=
 rnd_g r && (rnd_s r || negb (is_even (rnd_m r))).

Definition rndCU_fun (r : rnd_record) : bool :=
 rnd_g r.

Definition do_rnd (m : positive) (e : Z) (g : rnd_record -> bool) : float :=
 let r := rnd_aux m e in
 let f := Float (Z_of_N (rnd_m r)) (rnd_e r) in
 if (g r) then FSucc bound radix precision f else f.

Definition do_rnd2 (gp gn : rnd_record -> bool) (f : float) : float :=
 match (Fnum f) with
 | Z0 => Float 0 (-bExp)
 | Zpos p =>
  do_rnd p (Fexp f) gp
 | Zneg p =>
  Fopp (do_rnd p (Fexp f) gn)
 end.

Definition rndZ := do_rnd2 rndZ_fun rndZ_fun.
Definition rndU := do_rnd2 rndU_fun rndZ_fun.
Definition rndD := do_rnd2 rndZ_fun rndU_fun.
Definition rndO := do_rnd2 rndO_fun rndO_fun.
Definition rndCE := do_rnd2 rndCE_fun rndCE_fun.
Definition rndCU := do_rnd2 rndCU_fun rndCU_fun.

End F_rnd.
