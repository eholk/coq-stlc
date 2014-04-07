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
Qed.

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

