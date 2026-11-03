(** Generic differential test against the Lean oracle.

    For every generated input it checks:
    - generated [reference] and [check_invariant] = the Lean oracle, and the oracle says the
      input is inside [Bounded] (so the generator stays in the proved domain);
    - [plan] = [reference] whenever [check_invariant] holds;
    - [run] = [reference] always. *)

type report = {
  cases : int;
  invariant_held : int;
  invariant_broken : int;
  plan_differs_when_broken : int;
      (** Inputs where the plan alone would be wrong: shows the check is load-bearing. *)
  failures : string list;
}

let read_lines path =
  In_channel.with_open_text path In_channel.input_all
  |> String.split_on_char '\n'
  |> List.filter (fun l -> l <> "")

let oracle_outputs ~oracle ~name lines =
  let inp = Filename.temp_file "oracle" ".in" and out = Filename.temp_file "oracle" ".out" in
  Out_channel.with_open_text inp (fun oc -> List.iter (fun l -> output_string oc (l ^ "\n")) lines);
  let cmd = Filename.quote_command oracle [ name ] ~stdin:inp ~stdout:out in
  let code = Sys.command cmd in
  if code <> 0 then failwith (Printf.sprintf "oracle exited with %d: %s" code cmd);
  let res = read_lines out in
  Sys.remove inp;
  Sys.remove out;
  res

let shorten s = if String.length s <= 160 then s else String.sub s 0 160 ^ "..."

let run (type i o) (module S : Subject.S with type input = i and type output = o) ~oracle ~seed
    ~cases =
  let st = Random.State.make [| seed |] in
  let inputs =
    Array.init cases (fun k -> S.gen st ~size:(Pick.size st S.max_size) ~valid:(k mod 2 = 0))
  in
  let lines = Array.map S.to_line inputs in
  let expected = Array.of_list (oracle_outputs ~oracle ~name:S.name (Array.to_list lines)) in
  if Array.length expected <> cases then failwith "oracle returned a different number of lines";
  let failures = ref [] and held = ref 0 and differs = ref 0 in
  let fail k fmt =
    Printf.ksprintf
      (fun msg ->
        failures :=
          Printf.sprintf "%s seed=%d case=%d: %s; input: %s" S.name seed k msg
            (shorten lines.(k))
          :: !failures)
      fmt
  in
  Array.iteri
    (fun k input ->
      let r = S.reference input and c = S.check_invariant input in
      let got = Printf.sprintf "%s %b true" (S.show_output r) c in
      if got <> expected.(k) then fail k "generated (reference check bounded) = %S, Lean = %S" got expected.(k);
      let p = S.plan input in
      if c then (
        incr held;
        if not (S.equal_output p r) then
          fail k "invariant holds but plan = %s, reference = %s" (S.show_output p) (S.show_output r))
      else if not (S.equal_output p r) then incr differs;
      let u = S.run input in
      if not (S.equal_output u r) then
        fail k "run = %s, reference = %s" (S.show_output u) (S.show_output r))
    inputs;
  {
    cases;
    invariant_held = !held;
    invariant_broken = cases - !held;
    plan_differs_when_broken = !differs;
    failures = List.rev !failures;
  }
