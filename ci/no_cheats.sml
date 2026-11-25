(* Fails (exit code 1) if any theorem of the project depends on an oracle
   other than DISK_THM (the tag every theorem loaded from disk carries), e.g.
   a `cheat`.  Run with:  hol --holstate=$CAKEMLDIR/basis/basis-heap < no_cheats.sml *)
val thys = ["qsort", "qsortProg",
            "panLogic", "panQsortSpec", "panQsortProg", "panQsortProof"];
val _ = app (fn t => load (t ^ "Theory")) thys;

fun oracles th =
  List.filter (fn s => s <> "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)));

val all = List.concat (map (fn thy =>
            map (fn (n, th) => (thy ^ "." ^ n, th))
                (DB.theorems thy @ DB.definitions thy)) thys);

val bad = List.mapPartial
            (fn (n, th) => case oracles th of
                             [] => NONE
                           | os => SOME (n ^ " [" ^ String.concatWith "," os ^ "]"))
            all;

val _ =
  if null bad then
    (print ("no-cheats: OK, " ^ Int.toString (length all) ^
            " theorems/definitions checked\n");
     OS.Process.exit OS.Process.success)
  else
    (app (fn s => print ("depends on oracle: " ^ s ^ "\n")) bad;
     OS.Process.exit OS.Process.failure);
