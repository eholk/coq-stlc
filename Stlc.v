Require Import Decidable.

(* We don't need to be terribly specific so far... *)
Definition Symbol := Type.

Axiom sym_eq_dec: forall x y: Symbol, decidable (x = y).

Axiom sym_beq: Symbol -> Symbol -> bool.

Axiom sym_beq_eq: forall x y, (sym_beq x y = true) <-> x = y.

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

Definition apply_k (k: StepCont) : StepCont :=
  match k with
    | Error => Error
    | ApplyK EmptyK v => FinalK v
    | FinalK v => FinalK v
    | ApplyK (RatorK e2 env k) v => step e2 env (RandK v k)
    | ApplyK (RandK v' k) v => match v' with
                                 | Closure x b env =>
                                   step b (ExtendEnv Value x v env) k
                                 | _ => Error
                               end
  end.

Inductive steps_to_cont : StepCont -> Value -> Prop :=
| step_refl : forall v, steps_to_cont (FinalK v) v
| step_trans : forall s v, steps_to_cont (apply_k s) v -> steps_to_cont s v.

Definition steps_to e v := steps_to_cont (step e (EmptyEnv Value) EmptyK) v.


Inductive type_expr : (Env StlcType) -> Expr -> StlcType -> Prop :=
| type_unit : forall env, type_expr env Unit TUnit
| type_var : forall x t env, lookup x env = Some t -> type_expr env (Var x) t
| type_lambda : forall env x b t' t,
  type_expr (ExtendEnv _ x t' env) b t
  -> type_expr env (Lambda x b) (Fn t' t).

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
| type_empty_k : forall t, type_cont t EmptyK t.

Inductive type_step : StepCont -> StlcType -> Prop :=
| type_final : forall v t, type_value v t -> type_step (FinalK v) t
| type_apply : forall t' k v t,
  type_value v t' -> type_cont t' k t -> type_step (ApplyK k v) t.

Lemma preserve_step : forall t s s',
  type_step s t -> s' = apply_k s -> type_step s' t.
intros.
inversion H; subst; intros.
eauto using type_step.
inversion H2; subst.
simpl.
eauto using type_step.
Qed.

Lemma preserve_first : forall e t s,
  type_expr (EmptyEnv _) e t 
  -> step e (EmptyEnv _) EmptyK = s
  -> type_step s t.
intros.
inversion H; subst.
simpl.
apply (type_apply TUnit).
eauto using type_value.
eauto using type_cont.
contradict H1.
compute.
discriminate.
compute.
apply (type_apply (Fn t' t0)).
apply (type_closure _ _ _ (EmptyEnv StlcType)).
auto using related_env.
inversion H; subst.
apply H3.
eauto using type_cont.
Qed.

Lemma preserve_steps_to_cont : forall t s v,
  steps_to_cont s v ->
  type_step s t ->
  type_value v t.
intros.
induction H.
inversion H0; subst; auto.
apply IHsteps_to_cont.
apply (preserve_step _ _ (apply_k s)) in H0.
apply H0.
reflexivity.
Qed.

Theorem type_safe : forall e t v,
  type_expr (EmptyEnv StlcType) e t
  -> steps_to e v
  -> type_value v t.
intros e t v H.
inversion H; subst; intros.
compute in H0.
apply (preserve_steps_to_cont TUnit) in H0.
apply H0.
apply (type_apply TUnit).
eauto using type_value.
auto using type_cont.
compute in H0.
contradict H0; discriminate.
compute in H1.
apply (preserve_steps_to_cont (Fn t' t0)) in H1; auto.
apply (type_apply (Fn t' t0)).
apply (type_closure _ _ _ (EmptyEnv _)).
eauto using related_env.
auto.
eauto using type_cont.
Qed.
