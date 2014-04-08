Require Import Decidable.

(* We don't need to be terribly specific so far... *)
Definition Symbol := Type.

Axiom sym_eq_dec: forall x y: Symbol, decidable (x = y).

Axiom sym_beq: Symbol -> Symbol -> bool.

Axiom sym_beq_eq: forall x y, (sym_beq x y = true) <-> x = y.
Lemma sym_nbeq_neq: forall x y, (sym_beq x y = false) <-> x <> y.
intros.
split; intros.
intro.
case (sym_beq_eq x y); intros.
apply H2 in H0.
rewrite H0 in H.
contradict H.
discriminate.
case (sym_beq_eq x y); intros.
destruct (sym_beq x y).
contradict H.
auto.
auto.
Qed.

Inductive Expr :=
| Unit : Expr
| Var : Symbol -> Expr
| App : Expr -> Expr -> Expr
| Lambda : Symbol -> Expr -> Expr.

Lemma expr_eq_dec: forall e1 e2: Expr, decidable (e1 = e2).
intros; unfold decidable; decide equality.
apply sym_eq_dec.
apply sym_eq_dec.
Qed.

Inductive Env Val :=
| EmptyEnv : Env Val
| ExtendEnv : Symbol -> Val -> Env Val -> Env Val.

Lemma env_eq_dec T: forall (e1 e2 : Env T),
  (forall (v1 v2 : T), decidable (v1 = v2)) ->
  decidable (e1 = e2).
intros.
unfold decidable in H.
unfold decidable; decide equality.
apply sym_eq_dec.
Qed.

Inductive Value :=
| VUnit : Value
| Closure : Symbol -> Expr -> (Env Value) -> Value.

Inductive StlcType :=
| TUnit : StlcType
| Fn : StlcType -> StlcType -> StlcType.

Require Import Bool.BoolEq.

Fixpoint lookup {T: Type} (x: Symbol) (env: (Env T)) : option T.
intros.
destruct env.
refine None.
refine (if sym_beq x s then _ else _).
refine (Some t).
apply (lookup T x env).
Defined.

Inductive Cont :=
| EmptyK : Cont
| RatorK : Expr -> Env Value -> Cont -> Cont
| RandK : Value -> Cont -> Cont.

Inductive StepCont :=
| ApplyK : Cont -> Value -> StepCont
| FinalK : Value -> StepCont
| Error : StepCont.

Fixpoint step (e: Expr) (env : Env Value) (k: Cont) : StepCont :=
  match e with
    | Unit => ApplyK k VUnit
    | Var x => match lookup x env with
                 | Some v => ApplyK k v
                 | None => Error
               end
    | Lambda x b => ApplyK k (Closure x b env)
    | App e1 e2 => step e1 env (RatorK e2 env k)
  end.

Definition apply_k (k: Cont) v : StepCont :=
  match k with
    | EmptyK => FinalK v
    | RatorK e2 env k => step e2 env (RandK v k)
    | RandK v' k => match v' with
                      | Closure x b env =>
                        step b (ExtendEnv Value x v env) k
                      | _ => Error
                    end
  end.

Inductive step_cont : StepCont -> StepCont -> Prop :=
| step_refl : forall s, step_cont s s
| step_once : forall k v s,
  step_cont (apply_k k v) s -> step_cont (ApplyK k v) s.

Lemma step_trans : forall s1 s2 s3,
  step_cont s1 s2 -> step_cont s2 s3 -> step_cont s1 s3.
intros s1 s2 s3 H.
induction H; intros; inversion H; subst; eauto using step_cont.
Qed.

Inductive steps_to_cont : StepCont -> Value -> Prop :=
| step_final : forall v, steps_to_cont (FinalK v) v
| step_apply : forall k v' v,
  steps_to_cont (apply_k k v') v -> steps_to_cont (ApplyK k v') v.

Definition steps_to e env v := steps_to_cont (step e env EmptyK) v.


Inductive type_expr : (Env StlcType) -> Expr -> StlcType -> Prop :=
| type_unit : forall env, type_expr env Unit TUnit
| type_var : forall x t env, lookup x env = Some t -> type_expr env (Var x) t
| type_lambda : forall env x b t' t,
  type_expr (ExtendEnv _ x t' env) b t
  -> type_expr env (Lambda x b) (Fn t' t)
| type_app : forall e1 e2 t1 t2 env,
  type_expr env e1 (Fn t1 t2) -> type_expr env e2 t1
  -> type_expr env (App e1 e2) t2.

Inductive type_value : Value -> StlcType -> Prop :=
| type_vunit : type_value VUnit TUnit
| type_closure : forall x b env tenv t' t,
  related_env env tenv ->
  type_expr (ExtendEnv _ x t' tenv) b t ->
  type_value (Closure x b env) (Fn t' t)
with related_env : (Env Value) -> (Env StlcType) -> Prop :=
| relate_empty : related_env (EmptyEnv _) (EmptyEnv _)
| relate_extend : forall x v t env tenv,
  related_env env tenv ->
  type_value v t ->
  related_env (ExtendEnv _ x v env) (ExtendEnv _ x t tenv).

Inductive type_cont : (StlcType) -> Cont -> StlcType -> Prop :=
| type_empty_k : forall t, type_cont t EmptyK t
| type_ratork : forall t2 t1 e2 env tenv k t',
  related_env env tenv ->
  type_expr tenv e2 t2 ->
  type_cont t1 k t' ->
  type_cont (Fn t2 t1) (RatorK e2 env k) t'
| type_randk : forall t1 t2 t3 v k,
  type_cont t2 k t3 ->
  type_value v (Fn t1 t2) ->
  type_cont t1 (RandK v k) t3.

Inductive type_step : StepCont -> StlcType -> Prop :=
| type_final : forall v t, type_value v t -> type_step (FinalK v) t
| type_apply : forall t' k v t,
  type_value v t' -> type_cont t' k t -> type_step (ApplyK k v) t.

Require Import Setoid.

Lemma related_env_compat : forall env tenv,
  related_env env tenv ->
  forall x,
    (forall v, lookup x env = Some v -> exists t, lookup x tenv = Some t)
    /\
    (forall t, lookup x tenv = Some t -> exists v, lookup x env = Some v).
intros env tenv H; induction H; intros; split; intros.
contradict H; discriminate.
contradict H; discriminate.
case (sym_eq_dec x x0); intros; subst.
exists t; simpl.
assert (sym_beq x0 x0 = true).
apply sym_beq_eq; reflexivity.
rewrite H2; reflexivity.
simpl.
assert (sym_beq x0 x = false).
apply (sym_nbeq_neq x0 x).
intro; apply H2; auto.
rewrite H3.
destruct (IHrelated_env x0).
case (H4 v0); intros.
simpl in H1.
rewrite H3 in H1. exact H1.
exists x1; auto.
simpl.
destruct (sym_eq_dec x0 x).
rewrite H2.
assert (sym_beq x x = true).
apply (sym_beq_eq x x); auto.
rewrite H3.
exists v; auto.
assert (sym_beq x0 x = false).
apply (sym_nbeq_neq x0 x); auto.
rewrite H3.
destruct (IHrelated_env x0).
apply (H5 t0).
simpl in H1.
rewrite H3 in H1.
exact H1.
Qed.

Lemma related_env_equiv : forall env tenv,
  related_env env tenv ->
  forall x v t,
    lookup x env = Some v ->
    lookup x tenv = Some t ->
    type_value v t.
intros env tenv H;
induction H; intros.
contradict H0; simpl; discriminate.
destruct (sym_eq_dec x0 x); subst.
simpl in H1.
assert (sym_beq x x = true).
apply  (sym_beq_eq x x).
reflexivity.
rewrite H3 in H1.
injection H1; intros; subst.
simpl in H2.
rewrite H3 in H2; injection H2; intros; subst.
exact H0.
simpl in H1; simpl in H2.
assert (sym_beq x0 x = false).
apply (sym_nbeq_neq x0 x).
exact H3.
rewrite H4 in H1; rewrite H4 in H2.
apply (IHrelated_env x0).
exact H1.
exact H2.
Qed.

Lemma preserve_eval : forall e tenv t',
  type_expr tenv e t' ->
  forall env k t,
  related_env env tenv ->
  type_cont t' k t ->
  type_step (step e env k) t.
intros e tenv t' H.
induction H; intros; simpl.
apply (type_apply TUnit).
apply type_vunit.
auto.
case (related_env_compat env0 env H0 x); intros.
case (H3 t); auto; intros.
rewrite H4.
apply (type_apply t).
apply (related_env_equiv env0 env H0 x).
exact H4.
exact H.
exact H1.
simpl.
apply (type_apply (Fn t' t)).
apply (type_closure _ _ _ env); auto.
auto.
apply IHtype_expr1; auto.
apply (type_ratork _ _ _ _ env); auto.
Qed.

Lemma preserve_step : forall t k v,
  type_step (ApplyK k v) t -> type_step (apply_k k v) t.
intros.
inversion H; subst; simpl; eauto using type_step.
inversion H4; subst; eauto using type_step.
simpl.
apply (preserve_eval _ tenv t2); eauto using type_cont.
simpl.
inversion H4; subst; eauto using type_step.
inversion H9; subst; eauto using type_step.
apply (preserve_eval _ (ExtendEnv _ x t' tenv) t0); eauto using type_step.
eauto using related_env.
Qed.

Lemma preserve_first : forall e t,
  type_expr (EmptyEnv _) e t 
  -> type_step (step e (EmptyEnv _) EmptyK) t.
intros.
inversion H; subst.
unfold step.

apply (type_apply TUnit).
eauto using type_value.
eauto using type_cont.
contradict H0.
compute.
discriminate.
compute.
apply (type_apply (Fn t' t0)).
apply (type_closure _ _ _ (EmptyEnv StlcType)).
auto using related_env.
auto.
eauto using type_cont.
simpl.
apply (preserve_eval _ (EmptyEnv _) (Fn t1 t));
eauto using related_env, type_cont.
Qed.

Lemma preserve_steps_to_cont : forall t s v,
  steps_to_cont s v ->
  type_step s t ->
  type_value v t.
intros.
induction H.
inversion H0; subst; auto.
apply IHsteps_to_cont.
apply preserve_step.
apply H0.
Qed.

Lemma preserve_step1 :
  forall e env tenv k t' t, 
    related_env env tenv ->
    type_expr tenv e t' ->
    type_cont t' k t ->
    type_step (step e env k) t.
intro.
induction e; intros; simpl.
inversion H0; subst.
apply (type_apply TUnit); eauto using type_value.
inversion H0; subst.
case (related_env_compat env tenv H s); intros.
case (H3 t'); auto; intros.
rewrite H5.
apply (type_apply t').
apply (related_env_equiv env tenv H s); auto.
auto.
inversion H0; subst.
apply (IHe1 _ tenv _ (Fn t1 t')); auto.
apply (type_ratork _ _ _ _ tenv); auto.
apply (type_apply t').
inversion H0; subst; eauto using type_value.
auto.
Qed.

Theorem type_safe : forall e env tenv t,
  related_env env tenv ->
  type_expr tenv e t ->
  forall v, steps_to e env v -> type_value v t.
intro; induction e; intros; simpl.
inversion H0; subst.
inversion H1; subst.
simpl in H5.
inversion H5; subst; eauto using type_value.

inversion H0; subst.
inversion H1; subst.
contradict H3; destruct (lookup s env); discriminate.
assert (lookup s env = Some v).
destruct (lookup s env); try discriminate.
injection H2; intros; subst.
inversion H3; subst.
reflexivity.
apply (related_env_equiv env tenv H s); auto.

Focus 2.
inversion H1; subst.
inversion H5; subst.
inversion H0; subst.
apply (type_closure _ _ _ tenv); auto.

(* Application Line *)
generalize dependent e2.
generalize dependent e1.
intros.
unfold steps_to in H1.
apply (preserve_steps_to_cont _ (step (App e1 e2) env EmptyK)); auto.
apply (preserve_step1 _ _ tenv _ t); eauto using type_cont.
Qed.
