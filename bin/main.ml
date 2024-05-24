(* Temporal model checking for CTL, adapted from 
   https://www.cl.cam.ac.uk/teaching/2324/HLog+ModC/slides/lecture10.pdf *)

type state_t = int
module States = Set.Make(Int)

(* Temporal models (Kripke structures) over atomic propositions (state labels). *)
type 'ap temporal_model_t = {
  states : States.t;
  is_initial : state_t -> bool;
  can_transition : state_t -> state_t -> bool;
  has_label : state_t -> 'ap -> bool;
}

(* CTL* state propositions over atomic propositions. *)
type 'ap ctl_state_prop_t =
  | Label of 'ap
  | False 
  | True
  | Not of 'ap ctl_state_prop_t
  | Both of 'ap ctl_state_prop_t * 'ap ctl_state_prop_t
  | Either of 'ap ctl_state_prop_t * 'ap ctl_state_prop_t
  | If of 'ap ctl_state_prop_t * 'ap ctl_state_prop_t
  | Necessarily of 'ap ctl_path_prop_t
  | Possibly of 'ap ctl_path_prop_t
and 'ap ctl_path_prop_t =
  | Next of 'ap ctl_state_prop_t
  | Perpetually of 'ap ctl_state_prop_t
  | Eventually of 'ap ctl_state_prop_t
  | Until of 'ap ctl_state_prop_t * 'ap ctl_state_prop_t

(* Fixpoint of f; terminates if f is an endofunction on a finite state set. *)
let rec fix (f : States.t -> States.t) (states: States.t) : States.t =
  let new_states = f states in
  if States.equal states new_states then new_states else fix f new_states

let rec states_satisfying (model : 'ap temporal_model_t) (psi : 'ap ctl_state_prop_t) : States.t =
  match psi with
  | Label label -> States.filter (fun state -> model.has_label state label) model.states
  | True -> model.states (* Top set *)
  | False -> States.empty (* Bottom set *)
  | Not psi -> States.diff model.states (states_satisfying model psi) (* Complement *)
  | Both (psi_0, psi_1) -> States.inter (states_satisfying model psi_0) (states_satisfying model psi_1)
  | Either (psi_0, psi_1) -> States.union (states_satisfying model psi_0) (states_satisfying model psi_1)
  | If (psi_0, psi_1) -> states_satisfying model (Either (Not psi_0, psi_1))
  | Necessarily (Next psi) -> states_satisfying model (Not (Possibly (Next (Not psi))))
  | Necessarily (Perpetually psi) -> states_satisfying model (Not (Possibly (Eventually (Not psi))))
  | Necessarily (Eventually psi) -> states_satisfying model (Not (Possibly (Perpetually (Not psi))))
  | Necessarily (Until (psi_0, psi_1)) -> 
    (states_satisfying model (Both (Necessarily (Eventually psi_1), Not (Possibly (Until (Not psi_1, Not (Both (psi_0, psi_1))))))))
  | Possibly (Next psi) ->
    States.filter
      (fun state -> States.exists (model.can_transition state) (states_satisfying model psi))
      model.states
  | Possibly (Eventually psi) -> states_satisfying model (Possibly (Until (True, psi)))
  (* A state satisfying "possibly perpetually psi" is a state satisfying "psi" which can transition to
     a state satisfying "possibly perpetually psi" *)
  | Possibly (Perpetually psi) ->
    fix
      (fun states -> States.filter
        (fun state -> States.exists (model.can_transition state) states)
        states)
      (states_satisfying model psi)
  (* A state satisfying "possibly psi_0 until psi_1" is either a state satisfying "psi_1" or 
     a state satisfying "psi_0" which can transition to a state satisfying "possibly psi_0 until psi_1" *)
  | Possibly (Until (psi_0, psi_1)) ->
    let states_satisfying_psi_0 = states_satisfying model psi_0 in
    fix
      (fun states -> States.union
        (States.filter
          (fun state -> States.exists (model.can_transition state) states)
          states_satisfying_psi_0)
        states)
      (states_satisfying model psi_1)

let check_temporal_model (model: 'ap temporal_model_t) (psi : 'ap ctl_state_prop_t) : bool =
  (* Assert that the model's transition relation is left-total. *)
  assert (States.for_all (fun state -> States.exists (model.can_transition state) model.states) model.states);
  let states_satisfying_psi = states_satisfying model psi in
  States.for_all
    (fun initial_state -> States.mem initial_state states_satisfying_psi)
    (States.filter model.is_initial model.states)

type label_t = P

let model : label_t temporal_model_t = {
  states = States.(add 0 (add 1 (add 2 empty)));
  is_initial = (fun state -> state == 0);
  has_label = (fun state -> match state with
    | 0 -> fun p -> p == P
    | 1 -> fun _ -> false
    | 2 -> fun p-> p == P
    | _ -> fun _ -> false
  );
  can_transition = (fun state -> fun next_state -> match (state, next_state) with
    | (0, 0) -> true
    | (0, 1) -> true
    | (1, 2) -> true
    | (2, 2) -> true
    | _ -> false
  )
}

;;

print_endline (string_of_bool (check_temporal_model model (Necessarily (Eventually (Label P)))));;

print_endline (string_of_bool (check_temporal_model model (Necessarily (Eventually (Necessarily (Perpetually (Label P)))))));;
