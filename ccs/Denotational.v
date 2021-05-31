(* begin hide *)
From ITree Require Import
     ITree
     Eq.Eq
     Events.Exception
     ITreeFacts.

From CCS Require Import
     PropT
     Syntax
     Utils
.
Import ITreeNotations.
Open Scope itree.
Import CCSNotations.
Open Scope ccs_scope.

Section Semantics.

  Variant ActionE : Type -> Type :=
  | Act (a : action) : ActionE unit.

  Variant SynchE : Type -> Type := | Synch : SynchE unit.

  Variant choice := | Left | Right | Synchronize.

  Variant NonDetE : Type -> Type :=
  | Plus : NonDetE bool
  | Sched2 : NonDetE bool
  | Sched3 : NonDetE choice.

  Definition DeadE := exceptE unit.
  Definition dead {A : Type} {E} `{DeadE -< E} : itree E A :=
    x <- trigger (Throw tt);; match x: void with end.

  Notation ccsE   := (NonDetE +' ActionE +' SynchE +' DeadE).
  Notation ccsT T := (itree ccsE T).
  Notation ccs    := (ccsT unit).

  Definition done : ccs := Ret tt.

  Definition act (a : action) : ccs := trigger (Act a).

  Definition plus (P Q : ccs) : ccs :=
    b <- trigger Plus;;
    match b with
    | true => P
    | false => Q
    end.

  Definition branch2 (P Q : ccs) : ccs :=
    b <- trigger Sched2;;
    match b with
    | true => P
    | false => Q
    end.

  Definition branch3 (P Q R : ccs) : ccs :=
    b <- trigger Sched3;;
    match b with
    | Left => P
    | Right => Q
    | Synchronize => R
    end.

  Variant head :=
  | HDone
  | HSynch (P : ccs)
  | HAct (a : action) (P : ccs).

  (* Notations for patterns *)
  Notation "'schedP' e" := (inl1 e) (at level 10).
  Notation "'actP' e" := (inr1 (inl1 e)) (at level 10).
  Notation "'synchP' e" := (inr1 (inr1 (inl1 e))) (at level 10).
  Notation "'deadP' e" := (inr1 (inr1 (inr1 e))) (at level 10).

  Definition get_hd : ccs -> ccsT head :=
    cofix get_hd (P : ccs) :=
      match observe P with
      | RetF x => Ret HDone
      | TauF P => Tau (get_hd P)
      | @VisF _ _ _ T e k =>
        match e with
        | schedP e => vis e (fun x => get_hd (k x))
        | actP e =>
          match e in ActionE X return (T = X -> ccsT head) with
          | Act a => fun (Pf : T = unit) =>
                      Ret (HAct a (@eq_rect_r _ T (fun T => T -> itree ccsE unit) k unit (eq_sym Pf) tt))
          end eq_refl
        | synchP e =>
          match e in SynchE X return (T = X -> ccsT head) with
          | Synch => fun (Pf : T = unit) =>
                      Ret (HSynch (@eq_rect_r _ T (fun T => T -> itree ccsE unit) k unit (eq_sym Pf) tt))
          end eq_refl
        | deadP e => Ret HDone
        end
      end
  .

  Definition para_old : ccs -> ccs -> ccs :=
    cofix F (P : ccs) (Q : ccs) :=
      branch3
        (x <- get_hd P;;
         match x with
         | HDone => Q
         | HSynch P => vis Synch (fun _ => F P Q)
         | HAct a P => vis (Act a) (fun _ => F P Q)
         end
        )
        (x <- get_hd Q ;;
         match x with
         | HDone => P
         | HSynch Q => vis Synch (fun _ => F P Q)
         | HAct a Q => vis (Act a) (fun _ => F P Q)
         end
        )
        (rP <- get_hd P;;
         rQ <- get_hd Q;;
         match rP,rQ with
         | HAct a P, HAct b Q =>
           if are_opposite a b
           then vis Synch (fun _ => F P Q)
           else dead
         | _, _ => dead
         end
        )
  .

  Definition para : ccs -> ccs -> ccs :=
    cofix F (P : ccs) (Q : ccs) :=
      rP <- get_hd P;;
      rQ <- get_hd Q;;
      match rP, rQ with
      | HDone, HDone => done
      | HDone, _ => Q
      | _, HDone => P
      | HAct a P', HAct b Q' =>
        if are_opposite a b
        then
          branch3 (vis (Act a) (fun _ => F P' (vis (Act b) (fun _ => Q'))))
                  (vis (Act b) (fun _ => F (vis (Act a) (fun _ => P')) Q'))
                  (vis Synch   (fun _ => F P' Q'))
        else
          branch2 (vis (Act a) (fun _ => F P' (vis (Act b) (fun _ => Q'))))
                  (vis (Act b) (fun _ => F (vis (Act a) (fun _ => P')) Q'))
      | HAct a P', HSynch Q' =>
        branch2 (vis (Act a) (fun _ => F P' (vis Synch (fun _ => Q'))))
                (vis Synch   (fun _ => F (vis (Act a) (fun _ => P')) Q'))
      | HSynch P', HAct a Q' =>
        branch2 (vis Synch   (fun _ => F P' (vis (Act a) (fun _ => Q'))))
                (vis (Act a) (fun _ => F (vis Synch (fun _ => P')) Q'))
      | HSynch P', HSynch Q' =>
        branch2 (vis Synch   (fun _ => F P' (vis Synch (fun _ => Q'))))
                (vis Synch   (fun _ => F (vis Synch (fun _ => P')) Q'))
      end.

  Definition h_trigger {E F} `{E -< F} : E ~> itree F :=
    fun _ e => trigger e.

  Definition h_restrict (c : chan) : Handler ActionE ccsE :=
    fun _ e => let '(Act a) := e in
            match a with
            | Send c'
            | Rcv c' =>
              if c =? c' then dead else trigger e
            end.

  Definition restrict : chan -> ccs -> ccs :=
    fun c P =>
      interp (case_ h_trigger (case_ (h_restrict c) h_trigger)) P.

  Definition restrict' : chan -> ccs -> ccs.
    refine (cofix F c P :=
              match observe P with
              | RetF _ => done
              | TauF P => Tau (F c P)
              | @VisF _ _ _ T e k =>
                match e with
                | schedP e => _
                | actP e => let '(Act a) := e in
                           match a with
                           | Send c' | Rcv c' => if c =? c' then
                                                  dead
                                                else
                                                  vis e k
                           end
                | synchP e => vis e (fun x => F c (k x))
                | deadP e => P
                end
              end).
    refine (match e in NonDetE X return (T = X -> ccs) with
            | Plus => fun (b : T = bool) =>
                       let P : ccs := _ (* F c (k true) *) in
                       let Q : ccs := _ (* F c (k false) *) in
                       match (observe P, observe Q) with
                       | (VisF (deadP _) _, VisF (deadP _) _) => dead
                       | (VisF (deadP _) _, _) => Q
                       | (_, VisF (deadP _) _) => P
                       | (_, _) => branch2 P Q
                       end
            | Sched2 => fun (b : T = bool) =>
                         let P : ccs := _ (* F c (k true) *) in
                         let Q : ccs := _ (* F c (k false) *) in
                         match (observe P, observe Q) with
                         | (VisF (deadP _) _, VisF (deadP _) _) => dead
                         | (VisF (deadP _) _, _) => Q
                         | (_, VisF (deadP _) _) => P
                         | (_, _) => branch2 P Q
                         end
            | Sched3 => fun (b : T = choice) =>
                         let P : ccs := _ (* F c (k Left) *) in
                         let Q : ccs := _ (* F c (k Right) *) in
                         let R : ccs := _ (* F c (k Synchronize) *) in
                         match (observe P, observe Q, observe R) with
                         | (VisF (deadP _) _, VisF (deadP _) _, VisF (deadP _) _) => dead
                         (* this means there has been an internal communication on a restricted channel *)
                         | (VisF (deadP _) _, VisF (deadP _) _, _) => R
                         | (_, _, _) => branch3 P Q R
                         end
            end eq_refl).
    Guarded.
    (* TODO : finish this *)
    Abort.

  Fixpoint model (t : term) : ccs :=
    match t with
    | DoneT         => done
    | ActionT a t   => act a;; model t
    | ParaT t1 t2   => para (model t1) (model t2)
    | PlusT t1 t2   => plus (model t1) (model t2)
    | RestrictT c t => restrict c (model t)
    end.

  Fixpoint model_old (t : term) : ccs :=
    match t with
    | DoneT         => done
    | ActionT a t   => act a;; model_old t
    | ParaT t1 t2   => para_old (model_old t1) (model_old t2)
    | PlusT t1 t2   => plus (model_old t1) (model_old t2)
    | RestrictT c t => restrict c (model_old t)
    end.


  (** A term can advance in a single step producing either an action or a synchronisation,
   *  encoded here as None *)
  Inductive step : ccs -> option action -> ccs -> Prop :=
  (* Tau *)
  | S_Tau : forall a P Q, step P a Q -> step (Tau P) a Q
  (* Simple action *)
  | S_Vis_Act : forall a P, step (Vis (actP (Act a)) P) (Some a) (P tt)
  (* Synchronisation *)
  | S_Vis_Synch : forall P, step (Vis (synchP Synch) (fun _ => P)) None P
  (* Choice *)
  | S_Vis_Plus_L : forall a L L' R,
      step L a L' -> step (Vis (schedP Plus) (fun (b: bool) => if b then L else R)) a L'
  | S_Vis_Plus_R : forall a L R R',
      step R a R' -> step (Vis (schedP Plus) (fun (b: bool) => if b then L else R)) a R'
  (* Two-way parallelism *)
  | S_Vis_Sched2_L : forall a L L' R,
      step L a L' -> step (Vis (schedP Sched2) (fun (b: bool) => if b then L else R)) a L'
  | S_Vis_Sched2_R : forall a L R R',
      step R a R' -> step (Vis (schedP Sched2) (fun (b: bool) => if b then L else R)) a R'
  (* Three-way parallelism *)
  | S_Vis_Sched3_L : forall a L L' M R,
      step L a L' -> step (Vis (schedP Sched3) (fun c => match c with
                                                     | Left => L
                                                     | Synchronize => M
                                                     | Right => R
                                                     end)) a L'
  | S_Vis_Sched3_M : forall a L M M' R,
      step M a M' -> step (Vis (schedP Sched3) (fun c => match c with
                                                     | Left => L
                                                     | Synchronize => M
                                                     | Right => R
                                                     end)) a M'
  | S_Vis_Sched3_R : forall a L M R R',
      step R a R' -> step (Vis (schedP Sched3) (fun c => match c with
                                                     | Left => L
                                                     | Synchronize => M
                                                     | Right => R
                                                     end)) a R'.

End Semantics.

