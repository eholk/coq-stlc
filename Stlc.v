Require Import Decidable.
Require Import Bool.BoolEq.
Require Import Setoid.

(* We start off by defining symbols. 

We leave these largely undefined. Basically, we just need to be able
to tell whether two symbols are equal.

I feel like there is a better way to say "We have a type that has
these properties," but I'm not sure what that is in Coq. I want
something that's basically type classes. *)
Definition Symbol := Type.

Axiom sym_eq_dec: forall x y: Symbol, decidable (x = y).

Axiom sym_beq: Symbol -> Symbol -> bool.

(* We claim that our boolean equality function corresponds to actual
equality, and show that this also holds true for disequality. *)
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

(* We define expressions, which consist of variables, lambdas,
applications, and units. Unit creates an instance of the base type. *)
Inductive Expr :=
| Unit : Expr
| Var : Symbol -> Expr
| App : Expr -> Expr -> Expr
| Lambda : Symbol -> Expr -> Expr.

(* Both our interpreter and our typing rules will need
environments. We define environments to map symbols onto some other
thing, such as values or types. *)
Inductive Env Val :=
| EmptyEnv : Env Val
| ExtendEnv : Symbol -> Val -> Env Val -> Env Val.

(* There are two values: units and closures. *)
Inductive Value :=
| VUnit : Value
| Closure : Symbol -> Expr -> (Env Value) -> Value.

(* The two values correspond to two types, one for units and another
for closures. *)
Inductive StlcType :=
| TUnit : StlcType
| Fn : StlcType -> StlcType -> StlcType.

(* This is the function for looking up in an environment. I defined it
using tactics instead of writing it myself. *)
Fixpoint lookup {T: Type} (x: Symbol) (env: (Env T)) : option T.
intros.
destruct env.
refine None.
refine (if sym_beq x s then _ else _).
refine (Some t).
apply (lookup T x env).
(* Since we defined our function this way, it's good to look over it
and make sure we defined what we meant to. *)
Show Proof.
Defined.

(* To facilitate stepping through proofs, we define the interpreter in
continuation passing style, representing continuations as data
structures.

We define two functions, step and apply_k. Step takes an expression,
environment and continuation and returns a new continuation. Apply_k
takes one of these continuations and continues the computation.

Originally I defined step and apply_k as mutually recursive, but it
was tough to convince Coq that these would each terminate. Instead, I
split the result into two continuation types, and step returns an
ApplyK instead of directly calling apply_k. *)
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

(* This data type represents a proof that a continuation will result
in the given value if it executes long enough.

There are two branches: Either we are already at the final value, or
we have an ApplyK, meaning we need to take another step. *)
Inductive steps_to_cont : StepCont -> Value -> Prop :=
| step_final : forall v, steps_to_cont (FinalK v) v
| step_apply : forall k v' v,
  steps_to_cont (apply_k k v') v -> steps_to_cont (ApplyK k v') v.

Definition steps_to e env v := steps_to_cont (step e env EmptyK) v.

(* This type encodes the typing rules for STLC. There is one variant
for each of the inference rules. *)
Inductive type_expr : (Env StlcType) -> Expr -> StlcType -> Prop :=
| type_unit : forall env, type_expr env Unit TUnit
| type_var : forall x t env, lookup x env = Some t -> type_expr env (Var x) t
| type_lambda : forall env x b t' t,
  type_expr (ExtendEnv _ x t' env) b t
  -> type_expr env (Lambda x b) (Fn t' t)
| type_app : forall e1 e2 t1 t2 env,
  type_expr env e1 (Fn t1 t2) -> type_expr env e2 t1
  -> type_expr env (App e1 e2) t2.

(* For type safety, we want to prove that if an expression evaluates to a value, the value has the type it should. Thus, we need typing rules for values.

Closures include an environment, so we also need a way of relating
type environments to runtime environments. These are mutually
recursive because type checking closures needs a way to get a type
environment from the captured value environment, but the related
environment rules need to be able to typecheck values.

Alternatively, we could store the types in the value environment, but
my goal was to keep the typing rules and the interpreter entirely
separate. *)
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

(* We also need type checking rules for both types of continuations.

The first kind is expecting a value, so (type_cont t' k t) says that
continuation k will produce a value of type t if given a value of type
t'. *)
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

(* For step continuations, we just say that if this ran to completion
then we would get a value of type t. *)
Inductive type_step : StepCont -> StlcType -> Prop :=
| type_final : forall v t, type_value v t -> type_step (FinalK v) t
| type_apply : forall t' k v t,
  type_value v t' -> type_cont t' k t -> type_step (ApplyK k v) t.

(* These next two lemmas are very important. The first one says that
if a type and value environment are related and you look up a type in
the type environment, then you can also get a value from the value
environment, and vice-versa.

The second lemma says that if you look up a value and a type from
related environments, the value has the type from the type
environment. *)
Lemma related_env_compat : forall env tenv,
  related_env env tenv ->
  forall x,
    (forall v, lookup x env = Some v -> exists t, lookup x tenv = Some t)
    /\
    (forall t, lookup x tenv = Some t -> exists v, lookup x env = Some v).
(* This proof proceeds by induction on the related_environment judgment. *)
intros env tenv H; induction H; intros; split; intros.

(* This case is impossible because looking up anything in an empty
environment fails. *)
contradict H; discriminate.
(* This case is impossible for the same reason. *)
contradict H; discriminate.
(* Now we know that looking up in the environment gives us something,
but we need to consider whether we're at the current symbol or
not. This is what we get by destructing on (sym_eq_dec x x0). *)
case (sym_eq_dec x x0); intros; subst.
(* If they're equal, we know that t is the right type. We'll have to
do some simplification to make this clear to Coq though. *)
exists t; simpl.
assert (sym_beq x0 x0 = true).
apply sym_beq_eq; reflexivity.
rewrite H2; reflexivity.
(* Now we consider the case where the symbols x and x0 are not equal. *)
simpl.
assert (sym_beq x0 x = false).
apply (sym_nbeq_neq x0 x).
intro; apply H2; auto.
rewrite H3.
(* At this point we invoke the induction hypothesis to lookup in the
remainder of the environment. *)
destruct (IHrelated_env x0).
case (H4 v0); intros.
simpl in H1.
rewrite H3 in H1. exact H1.
exists x1; auto.
(* Now we repeat the process for value environments. *)
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

(* This is the second part, if you get a type and a value from two
related environments, they go together. *)
Lemma related_env_equiv : forall env tenv,
  related_env env tenv ->
  forall x v t,
    lookup x env = Some v ->
    lookup x tenv = Some t ->
    type_value v t.
(* Again, by induction on the related_env judgment *)
intros env tenv H;
induction H; intros.
(* This case is obviously impossible *)
contradict H0; simpl; discriminate.
(* Again, consider the case where x0 = x and x0 <> x *)
destruct (sym_eq_dec x0 x); subst.
simpl in H1.
assert (sym_beq x x = true).
apply  (sym_beq_eq x x).
reflexivity.
rewrite H3 in H1.
(* Injection says that since Some v = Some v0, v must equal v0 *)
injection H1; intros; subst.
simpl in H2.
rewrite H3 in H2; injection H2; intros; subst.
exact H0.
(* Now we consider where x0 <> x *)
simpl in H1; simpl in H2.
assert (sym_beq x0 x = false).
apply (sym_nbeq_neq x0 x).
exact H3.
rewrite H4 in H1; rewrite H4 in H2.
(* We use the induction hypothesis to search the rest of the environment. *)
apply (IHrelated_env x0).
exact H1.
exact H2.
Qed.

(* Next we have a bunch of preservation lemmas. We have a couple of
ways of taking steps, so each of these say that the types do not
change as we do this. *)

Lemma preserve_eval : forall e tenv t',
  type_expr tenv e t' ->
  forall env k t,
  related_env env tenv ->
  type_cont t' k t ->
  type_step (step e env k) t.
intros e tenv t' H.
(* By induction on the typing of expressions *)
induction H; intros; simpl.
apply (type_apply TUnit).
apply type_vunit.
auto.
(* Here's a case of us using the related_env_compat lemmas from above
to show we can get a value of of env0. *)
case (related_env_compat env0 env H0 x); intros.
(* case (H3 t) let's us talk about the value that related_env_compat
guarantees must exist. *)
case (H3 t); auto; intros.
rewrite H4.
apply (type_apply t).
(* We know this value has the right type, because we pulled it from a
related environment. *)
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
(* By induction over the typing rules for step continuation. We use
eauto to dispatch the easy cases automatically. *)
inversion H; subst; simpl; eauto using type_step.
(* The inversion tactic tells us which cases would have led to H4
being true. Once again, eauto helps us dispatch the easy cases. *)
inversion H4; subst; eauto using type_step.

simpl.
apply (preserve_eval _ tenv t2); eauto using type_cont.

simpl.
inversion H4; subst; eauto using type_step.
inversion H9; subst; eauto using type_step.
apply (preserve_eval _ (ExtendEnv _ x t' tenv) t0); eauto using type_step.
eauto using related_env.
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

(* Finally, we can prove type safety *)
Theorem type_safe : forall e env tenv t,
  related_env env tenv ->
  type_expr tenv e t ->
  forall v, steps_to e env v -> type_value v t.
(* We go by induction over expressions. *)
intro; induction e; intros; simpl.

(* Unit Case *)
inversion H0; subst.
inversion H1; subst.
simpl in H5.
inversion H5; subst; eauto using type_value.

(* Variable Lookup Case *)
inversion H0; subst.
inversion H1; subst.
(* H3 is a impossible, since there is no way to make a FinalK equal to
a ApplyK or an Error. discriminate is a useful tactic to prove things
aren't equal. *)
contradict H3; destruct (lookup s env); discriminate.
assert (lookup s env = Some v).
(* The `; try discriminate` attempts to automatically dispatch that
case, letting us look at the slightly more interesting one. *)
destruct (lookup s env); try discriminate.
injection H2; intros; subst.
inversion H3; subst.
reflexivity.
apply (related_env_equiv env tenv H s); auto.

(* Coq wants us to do the application line next, but that's hard, so
we'll tackle the easy Lambda case first. *)
Focus 2.
inversion H1; subst.
inversion H5; subst.
inversion H0; subst.
apply (type_closure _ _ _ tenv); auto.

(* Application Line *)
unfold steps_to in H1.
apply (preserve_steps_to_cont _ (step (App e1 e2) env EmptyK)); auto.
apply (preserve_step1 _ _ tenv _ t); eauto using type_cont.
(* Actually, that wasn't so hard, since most of the work was in the
preservation lemmas. *)
Qed.
