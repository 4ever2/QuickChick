open Pp
open Loc
open Names
open Extract_env
open Tacmach
open Entries
open Declarations
open Declare
open Libnames
open Util
open Constrintern
open Topconstr
open Constrexpr
open Constrexpr_ops
open Decl_kinds
open GenericLib
open SetLib
open CoqLib

(* TODO : move to utils or smth *)
type name_provider = { next_name : unit -> string }

let mk_name_provider s = 
  let cnt = ref 0 in
  { next_name = fun () -> 
      let res = Printf.sprintf "%s_%d_" s !cnt in
      incr cnt;
      res
  }

(* Advanced Generators *)

(* Ranges are undefined, unknowns or constructors applied to ranges *)
module Unknown = struct 
  type t = var 
  
  let to_string = var_to_string
  let from_string x = fresh_name x
  let from_var x = x

  let undefined = fresh_name "Ireallywantundefinedherebutwedonthavelaziness"

end

module UnknownOrd = struct
  type t = Unknown.t
  let compare x y = compare (Unknown.to_string x) (Unknown.to_string y)
end

type unknown = Unknown.t

type range = Ctr of constructor * range list | Unknown of unknown | Undef of dep_type | FixedInput

let rec range_to_string = function
  | Ctr (c, rs) -> constructor_to_string c ^ " " ^ str_lst_to_string " " (List.map range_to_string rs)
  | Unknown u -> Unknown.to_string u
  | Undef dt -> Printf.sprintf "Undef (%s)" (dep_type_to_string dt)
  | FixedInput -> "FixedInput"
  
module UM = Map.Make(UnknownOrd)

type umap = range UM.t

let lookup k m = try Some (UM.find k m) with Not_found -> None

(* For equality handling: require ordered (String, String) *)
module OrdTSS = struct 
  type t = unknown * unknown
  let compare x y = compare x y
end

module EqSet = Set.Make(OrdTSS)

let eq_set_add u1 u2 eqs = 
  let (u1', u2') = if u1 < u2 then (u1, u2) else (u2, u1) in
  EqSet.add (u1', u2') eqs

module OrdTyp = struct 
  type t = dep_type
  let compare = compare
end

module ArbSet = Set.Make(OrdTyp)             


type unknown_provider = { next_unknown : unit -> Unknown.t }

let unk_provider = 
  let np = mk_name_provider "unkn" in
  { next_unknown = fun () -> Unknown.from_string (np.next_name ()) }

(* Match a constructor/ranges list to a fixed input *)
(* Range list is toplevel, so it's mostly unifications.
   If any of the unknowns in rs is "FixedInput", then 
   we need to create a fresh unknown, bind it to the other unknown and 
   raise an equality check *)
let rec raiseMatch (k : umap) (c : constructor) (rs : range list) (eqs: EqSet.t) 
        : (umap * matcher_pat * EqSet.t) option = 
  foldM (fun (k, l, eqs) r ->
         match r with 
         | Ctr (c', rs') ->
            raiseMatch k c' rs' eqs >>= fun (k', m, eqs') ->
            Some (k', m::l, eqs')
         | Unknown u ->
            lookup u k >>= fun r' ->
            begin match r' with 
            | Undef _ -> (* The unknown should now be fixed *)
               Some (UM.add u FixedInput k, (MatchU u)::l, eqs)
            | FixedInput -> (* The unknown is already fixed, raise an eq check *)
               let u' = unk_provider.next_unknown () in
               Some (UM.add u' (Unknown u) k, (MatchU u')::l, eq_set_add u' u eqs)
            | _ -> failwith "Not supported yet"
            end
        ) (Some (k, [], eqs)) rs >>= fun (k', l, eqs') ->
  Some (k', MatchCtr (c, List.rev l), eqs')

(* Invariants: 
   -- Everything has a binding, even if just Undef 
   -- r1, r2 are never FixedInput, Undef (handled inline)
   -- TopLevel ranges can be unknowns or constructors applied to toplevel ranges
   -- Constructor bindings in umaps are also toplevel. 
   -- Only unknowns can be bound to Undef/FixedInput
*)
let rec unify (k : umap) (r1 : range) (r2 : range) (eqs : EqSet.t)
        : (umap * range * EqSet.t * (unknown * matcher_pat) list) option =
  msgerr (str (Printf.sprintf "Calling unify with %s %s" (range_to_string r1) (range_to_string r2)) ++ fnl ());
  match r1, r2 with
  | Unknown u1, Unknown u2 ->
     if u1 == u2 then Some (k, Unknown u1, eqs, []) else
     lookup u1 k >>= fun r1 -> 
     lookup u2 k >>= fun r2 ->
     begin match r1, r2 with 
     (* "Delay" cases - unknowns call unify again *)
     (* TODO: rething return value *)
     | Unknown u1', _ -> 
        unify k (Unknown u1') r2 eqs >>= fun (k', r', eqs', ms') ->
        Some (k', Unknown u1, eqs', ms')
     | _, Unknown u2' ->
        unify k r1 (Unknown u2') eqs >>= fun (k', r', eqs', ms') ->
        Some (k', Unknown u2, eqs', ms')

     (* "Hard" case: both are fixed. Need to raise an equality check on the inputs *)
     | FixedInput, FixedInput -> 
        let (u1', u2') = if u1 < u2 then (u1, u2) else (u2, u1) in
        (* Need to insert an equality between u1 and u2 *)
        let eqs' = EqSet.add (u1, u2) eqs in 
        (* Unify them in k *)
        Some (UM.add u1' (Unknown u2') k, Unknown u1', eqs', [])

     (* Easy cases: When at least one is undefined, it binds to the other *)
     (* Can probably replace fixed input with _ *)
     | Undef _ , Undef _ ->
        let (u1', u2') = if u1 < u2 then (u1, u2) else (u2, u1) in
        Some (UM.add u1' (Unknown u2') k, Unknown u1', eqs, [])
     | _, Undef _ ->
        Some (UM.add u2 (Unknown u1) k, Unknown u2, eqs, [])
     | Undef _, _ ->
        Some (UM.add u1 (Unknown u2) k, Unknown u1, eqs, [])

     (* Constructor bindings *) 
     | Ctr (c1, rs1), Ctr (c2, rs2) ->
        if c1 == c2 then 
          foldM (fun b a -> let (r1, r2) = a in 
                            let (k, l, eqs, ms) = b in 
                            unify k r1 r2 eqs >>= fun res ->
                            let (k', r', eqs', ms') = res in 
                            Some (k', r'::l, eqs', ms @ ms')
                ) (Some (k, [], eqs, [])) (List.combine rs1 rs2) >>= fun (k', rs', eqs', ms) ->
          Some (k', Ctr (c1, List.rev rs'), eqs', ms)
        else None

     (* Last hard cases: Constructors vs fixed *) 
     | FixedInput, Ctr (c, rs) ->
        (* Raises a match and potential equalities *)
        raiseMatch k c rs eqs >>= fun (k', m, eqs') ->
        Some (UM.add u1 (Unknown u2) k', Unknown u1, eqs', [(u1, m)])
     | Ctr (c, rs), FixedInput ->
        (* Raises a match and potential equalities *)
        raiseMatch k c rs eqs >>= fun (k', m, eqs') ->
        Some (UM.add u2 (Unknown u1) k', Unknown u2, eqs', [(u2, m)])
     end
   | Ctr (c1, rs1), Ctr (c2, rs2) ->
      if c1 == c2 then 
        foldM (fun b a -> let (r1, r2) = a in 
                          let (k, l, eqs, ms) = b in 
                          unify k r1 r2 eqs >>= fun res ->
                          let (k', r', eqs', ms') = res in 
                          Some (k', r'::l, eqs', ms @ ms')
              ) (Some (k, [], eqs, [])) (List.combine rs1 rs2) >>= fun (k', rs', eqs', ms) ->
        Some (k', Ctr (c1, List.rev rs'), eqs', ms)
      else None
   | Unknown u, Ctr (c, rs) 
   | Ctr (c, rs), Unknown u ->
      lookup u k >>= fun r ->
      begin match r with 
      | FixedInput -> 
        (* Raises a match and potential equalities *)
        raiseMatch k c rs eqs >>= fun (k', m, eqs') ->
        Some (UM.add u (Ctr (c,rs)) k', Unknown u, eqs', [(u, m)])
      | Undef _ -> Some (UM.add u (Ctr (c,rs)) k, Unknown u, eqs, [])
      | Ctr (c', rs') -> 
        if c == c' then 
          foldM (fun b a -> let (r1, r2) = a in 
                            let (k, l, eqs, ms) = b in 
                            unify k r1 r2 eqs >>= fun res ->
                            let (k', r', eqs', ms') = res in 
                            Some (k', r'::l, eqs', ms @ ms')
                ) (Some (k, [], eqs, [])) (List.combine rs rs') >>= fun (k', rs', eqs', ms) ->
          Some (k', Unknown u, eqs', ms)
        else None
      | Unknown u' -> 
         unify k (Ctr (c,rs)) (Unknown u') eqs >>= fun (k', r', eqs', m') ->
         Some (k', Unknown u, eqs', m')
      end

let rec fixRange u r k = 
    match r with 
    | FixedInput -> k
    | Undef _ -> UM.add u FixedInput k 
    | Unknown u' -> fixRange u' (UM.find u' k) k
    | Ctr (_, rs) -> List.fold_left (fun k r -> fixRange Unknown.undefined r k) k rs 

let fixVariable x k = fixRange x (UM.find x k) k

let rec convert_to_range dt = 
  match dt with 
  | DTyVar x -> Unknown x
  | DCtr (c,dts) -> Ctr (c, List.map convert_to_range dts)
  | DTyCtr (c, dts) -> Ctr (injectCtr (ty_ctr_to_string c), List.map convert_to_range dts)
  | _ -> failwith ("Unsupported range: " ^ (dep_type_to_string dt))

let is_fixed k dt = 
  let rec aux = function
    | Undef _ -> false
    | FixedInput -> true
    | Unknown u' -> aux (UM.find u' k)
    | Ctr (_, rs) -> List.for_all aux rs
  in aux (convert_to_range dt)

(* convert a range to a coq expression *)
let rec range_to_coq_expr k r = 
  match r with 
  | Ctr (c, rs) -> 
     gApp (gCtr c) (List.map (range_to_coq_expr k) rs)
  | Unknown u -> 
     begin match UM.find u k with
     | FixedInput -> gVar u
     | Undef _ -> (msgerr (str "It's stupid that this is called" ++ fnl ()); gVar u)
     | Unknown u' -> range_to_coq_expr k (Unknown u')
     | Ctr (c, rs) -> gApp (gCtr c) (List.map (range_to_coq_expr k) rs)
     end

let rec dt_to_coq_expr k dt = 
  range_to_coq_expr k (convert_to_range dt)

let rec is_dep_type = function
  | DArrow (dt1, dt2) -> is_dep_type dt1 || is_dep_type dt2 
  | DProd ((_, dt1), dt2) -> is_dep_type dt1 || is_dep_type dt2 
  | DTyParam _ -> false
  | DTyVar _ -> true
  | DCtr _ -> true
  | DTyCtr (_, dts) -> List.exists is_dep_type dts
  | DApp (dt, dts) -> List.exists is_dep_type (dt::dts)
  | DNot dt -> is_dep_type dt

let need_dec = ref false

let arbitrarySizedST gen_ctr dep_type gen_type ctrs input_names inputs n register_arbitrary =
  let gen = mk_name_provider "gen" in
  let dec = mk_name_provider "dec" in
  let arb = mk_name_provider "arb" in
  let input_names = List.map fresh_name input_names in

  let rec_dec_name = gInject (Printf.sprintf "depDec%n" (dep_type_len dep_type)) in

  let forGen = Unknown.from_string "_forGen" in

  let rec inputWithGen i l = 
    if i <= 1 then forGen :: l
    else let (h::t) = l in h :: (inputWithGen (i-1) t) in

  (* Handling a branch: returns the generator and a boolean (true if base branch) *)
  let handle_branch size rec_name (c : dep_ctr) : (coq_expr * bool) = 
    let (ctr, typ) = c in
    let b = ref true in 

    msgerr (str "Debug branch" ++ fnl ());

    let register_unknowns map = 
      let rec aux map = function
        | DArrow (dt1, dt2) -> aux map dt2
        | DProd ((x, dt1), dt2) -> aux (UM.add x (Undef dt1) map) dt2
        | _ -> map in
      aux map typ
    in

    let init_map = UM.add forGen (Undef (nthType n dep_type)) 
                                 (List.fold_left (fun m n -> UM.add n FixedInput m) 
                                                 (register_unknowns UM.empty) input_names) 
    in

    msgerr (str ("Calculating ranges: " ^ dep_type_to_string (dep_result_type typ)) ++ fnl ());
    let ranges = match dep_result_type typ with
      | DTyCtr (_, dts) -> List.map convert_to_range dts
      | _ -> failwith "Not the expected result type" in

    let inputsWithGen = inputWithGen n input_names in

    (* Debugging init map *)
    msgerr (str ("Handling branch: " ^ dep_type_to_string typ) ++ fnl ());
    UM.iter (fun x r -> msgerr (str ("Bound: " ^ (var_to_string x) ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) init_map;
    dep_fold_ty (fun _ dt1 -> msgerr (str (Printf.sprintf "%s : %b\n" (dep_type_to_string dt1) (is_dep_type dt1)) ++ fnl()))
                (fun _ _ dt1 -> msgerr (str (Printf.sprintf "%s : %b\n" (dep_type_to_string dt1) (is_dep_type dt1)) ++ fnl()))
                (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) typ;
    (* End debugging *)

    match foldM (fun (k, eqs, ms) (r, n) -> unify k (Unknown n) r eqs >>= fun (k', _, eqs', ms') ->
                                      Some (k', eqs', ms @ ms')
          ) (Some (init_map, EqSet.empty, [])) (List.combine ranges inputsWithGen) with
    | None -> failwith "Matching result type error" 
    | Some (map, eqs, matches) -> 

    (* Construct equalities *)

    (* Function to instantiate a single range *)
    let rec instantiate_range_cont (k : umap) (parent : unknown) (cont : umap -> coq_expr -> coq_expr) = function
      | Ctr (c,rs) -> 
         (* aux2 goes through the dts, enhancing the continuation to include the result of the head to the acc *)
         let rec traverse_ranges k acc = function 
           | [] -> cont k (gApp ~explicit:true (gCtr c) (List.rev acc)) (* Something about type parameters? *)
           | r::rest -> instantiate_range_cont k Unknown.undefined (fun k hg -> traverse_ranges k (hg::acc) rest) r
         in traverse_ranges k [] rs
      | Undef dt -> 
         register_arbitrary dt; 
         let arb = arb.next_name () in
         let k' = UM.add parent (Unknown (fresh_name arb)) (UM.add (fresh_name arb) FixedInput k) in
         bindGen (gInject "arbitrary") arb (fun arb -> cont k' (gVar arb))
      | Unknown u -> instantiate_range_cont k u cont (UM.find u k)
      | FixedInput -> cont k (gVar parent)
    in 

    let instantiate_range k r = 
      instantiate_range_cont k Unknown.undefined (fun k c -> returnGen (gSome c)) r
    in

    let rec combine_inductives k num_dts args = 
      match num_dts, args with 
      | [], _ -> []
      | (_,dt)::dts', arg::args' -> 
         if is_inductive_dt dt then dt_to_coq_expr k dt :: combine_inductives k dts' args
         else gVar arg :: combine_inductives k dts' args'
    in 

    let rec handle_TyCtr pos c dts k dt2 rec_name = 
      let numbered_dts = List.mapi (fun i dt -> (i+1, dt)) dts in (* +1 because of nth being 1-indexed *)

      (* Construct the checker for the current type constructor *)
      let checker args = 
        gApp ~explicit:true (gInject (Printf.sprintf "depDec%n" (List.length numbered_dts))) (
             (* A, B, ...: Type *)
             List.map (fun _ -> hole) args @ 

             (* P : forall A B : Prop *)
             [ gFun (List.flatten (List.map (fun (j,dt) -> if is_inductive_dt dt then [] 
                                                           else [var_to_string (make_up_name ())]) numbered_dts))
                    (fun args -> gApp ~explicit:true (gTyCtr c) (combine_inductives k numbered_dts args))

             (* Instance *)
             ; hole 

             (* Actual arguments to checker *)
             ] 
             @ args)
      in 

      match List.filter (fun (i, dt) -> not (is_fixed k dt)) numbered_dts with
      | [] -> (* Every argument to the constructor is fixed - perform a check *)

         (* Check if we are handling the current constructor. If yes, mark the need for decidability of current constructor *)
         (* need_dec is a ref in scope *)
         if c == gen_ctr then (need_dec := true; b := false) else ();

         (* Continuation handling dt2 : recurse one dt2 / None based on positivity *)
         let body_cont = recurse_type k dt2 in
         let body_fail = returnGen gNone in

         (* Perform the check - rec_dec_name is in scope *)
         gMatch (checker (List.map (fun dt -> dt_to_coq_expr k dt) dts))
                [ (injectCtr "left", ["eq" ] , fun _ -> if pos then body_cont else body_fail)
                ; (injectCtr "right", ["neq"], fun _ -> if pos then body_fail else body_cont) 
                ]

      | [(i, DTyVar x)] -> (* Single variable to be generated for *)
         if i == n && c == gen_ctr && pos then begin (* Recursive call *)
           b := false;
           let args = List.map snd (List.filter (fun (i, _) -> not (i == n)) (List.mapi (fun i dt -> (i+1, dt_to_coq_expr k dt)) dts)) in
           bindGenOpt (gApp (gVar rec_name) (gVar size :: args)) (var_to_string x) 
                      (fun _ -> recurse_type (fixVariable x k) dt2)
         end
         else if pos then begin (* Generate using "arbitrarySizeST" and annotations for type *)
           if c = gen_ctr then b := false;
           (* @arbitrarySizeST {A} (P : A -> Prop) {Instance} (size : nat) -> G (option A) *)
           bindGenOpt (gApp ~explicit:true (gInject "arbitrarySizeST")
                            [ hole (* Implicit argument - type A *)
                            ; gFun [var_to_string x] (fun [x] -> 
                                gApp (gTyCtr c) (List.map (fun (j, dt) -> 
                                  (* Replace the i-th variable with x - we're creating fun x => c dt_1 dt_2 ... x dt_{i+1} ... *)
                                  if i == j then gVar x else dt_to_coq_expr k dt
                                ) numbered_dts))
                            ; hole (* Implicit instance *)
                            ; gVar size ]
                      ) 
                      (var_to_string x)
                      (fun x -> (* [x] should be the same as the previous x - var_to_string *)
                        recurse_type (fixVariable x k) dt2
                      )
         end
         else (* Negation. Since we expect the *positive* versions to be sparse, we can use suchThatMaybe for negative *)
           (* TODO: something about size? *)
           bindGenOpt (gApp (gInject "suchThatMaybe") 
                            [ gInject "arbitrary" (* generate using "arbitrary" *)
                            ; gFun [var_to_string x] (fun [x] -> 
                                checker (List.map (fun (j,dt) -> if i == j then gVar x else dt_to_coq_expr k dt) numbered_dts)
                              )
                            ])
                      (var_to_string x)
                      (fun x -> recurse_type (fixVariable x k) dt2)

      | [(i, dt) ] -> failwith ("Internal error: not a variable to be generated for" ^ (dep_type_to_string dt)) 
         
      (* Multiple arguments to be generated for. Generalized arbitrarySizeST? *)
      | filtered -> begin
         (* For now, check if n is in the filtered list *)
         match List.filter (fun (i,dt) -> i == n) filtered with 
         | [(_, DTyVar x)] -> 
            b := false; 
            (* Every other variable generated using "arbitrary" *)
            let rec build_arbs k acc = function 
              | [] -> 
                 (* base case - recursive call *)
                 if pos then 
                   bindGenOpt (gApp (gVar rec_name) (gVar size :: List.rev acc))
                                   (var_to_string x)
                                   (fun _ -> recurse_type (fixVariable x k) dt2)
                 else failwith "Negation / build_arbs"
              | (i,dt)::rest -> 
                 if i == n then build_arbs k acc rest (* Recursive argument - handle at the end *)
                 else if is_fixed k dt then (* Fixed argument - do nothing *)
                   build_arbs k (dt_to_coq_expr k dt :: acc) rest 
                 else (* Call arbitrary and bind it to a new name *)
                   let arb = arb.next_name () in
                   let rdt = convert_to_range dt in
                   instantiate_range_cont k Unknown.undefined 
                     (fun k c -> (* Continuation: call build_arbs on the rest *)
                        build_arbs k (c :: acc) rest
                     ) rdt
            in build_arbs k [] numbered_dts
         | _ -> failwith "Mode analysis failure"
      end

    (* Dispatcher for constraints *)
    and handle_dt pos dt1 dt2 k rec_name = 
      match dt1 with 
      | DTyCtr (c,dts) -> 
         handle_TyCtr pos c dts k dt2 rec_name 
      | DNot dt -> 
         handle_dt (not pos) dt dt2 k rec_name
      | _ -> failwith "Constraints should be type constructors/negations"

    (* Iterate through constraints *)
    and recurse_type k = function
      | DProd (_, dt) -> (* Only introduces variables, doesn't constrain them *)
         recurse_type k dt 
      | DArrow (dt1, dt2) -> 
         msgerr (str ("Darrowing: " ^ range_to_string (UM.find forGen k)) ++ fnl ());
         handle_dt true dt1 dt2 k rec_name
      | DTyCtr _ -> (* result *) 
         instantiate_range k (Unknown forGen) (* result *)
      | _ -> failwith "Wrong type" in

    (* TODO: Whenn handling parameters, this might need to add additional arguments *)
    let handle_equalities eqs c = 
      EqSet.fold (fun (u1,u2) c -> 
                  let check = gApp ~explicit:true (gInject "depDec2") [hole; hole; 
                                                                       gFun ["x"; "y"] (fun [x;y] -> gApp (gInject "eq") [gVar x; gVar y]);
                                                                       hole;
                                                                       gVar u1; gVar u2] in
                 gMatch check 
                        [ (injectCtr "left" , ["eq" ], fun _ -> c)
                        ; (injectCtr "right", ["neq"], fun _ -> returnGen gNone) ]
                 ) eqs c in

    let branch_gen = 
      let rec walk_matches = function
        | [] -> handle_equalities eqs (recurse_type map typ)
        | (u,m)::ms -> begin 
            msgerr (str (Printf.sprintf "Processing Match: %s @ %s" (Unknown.to_string u) (matcher_pat_to_string m)) ++ fnl ());
            construct_match (gVar u) ~catch_all:(Some (returnGen gNone)) [(m,walk_matches ms)]
          end in
      walk_matches matches
    in 
    
    (* Debugging resulting match *)
    UM.iter (fun x r -> msgerr (str ("Bound: " ^ var_to_string x ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) map;
    EqSet.iter (fun (u,u') -> msgerr (str (Printf.sprintf "Eq: %s = %s\n" (Unknown.to_string u) (Unknown.to_string u')) ++ fnl())) eqs;
    List.iter (fun (u,m) -> msgerr (str ((Unknown.to_string u) ^ (matcher_pat_to_string m)) ++ fnl ())) matches;

    msgerr (str "Generated..." ++ fnl ());
    debug_coq_expr branch_gen;
    (* End debugging *)

    (branch_gen ,!b)
  in

  (*  List.iter (fun x -> ignore (handle_branch x)) ctrs;  *)

  let aux_arb rec_name size vars = 
    gMatch (gVar size) 
           [ (injectCtr "O", [], 
              fun _ -> (* Base cases *) 
              let base_branches = List.map fst (List.filter (fun (_, b) -> b) (List.map (handle_branch size rec_name) ctrs)) in
              uniform_backtracking base_branches
             )
           ; (injectCtr "S", ["size'"], 
              fun [size'] -> 
              let all_branches = List.map (fun x -> fst (handle_branch size' rec_name x)) ctrs in
              uniform_backtracking all_branches
             )
           ] in

  let generator_body = gRecFunInWithArgs
                    ~assumType:(gen_type)
                    "aux_arb" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
                    (fun (rec_name, size::vars) -> aux_arb rec_name size vars)
                    (fun rec_name -> gFun ["size"] 
                                    (fun [size] -> gApp (gVar rec_name) 
                                                        (gVar size :: List.map gVar input_names)
                                    ))
  in

  msgerr (fnl () ++ fnl () ++ str "`Final body produced:" ++ fnl ());
  debug_coq_expr generator_body;                       
  msgerr (fnl ());
  gRecord [("arbitrarySizeST", generator_body)]
