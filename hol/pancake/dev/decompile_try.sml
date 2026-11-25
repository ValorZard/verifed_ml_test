(* Experiment (not part of the build or CI): run CakeML's proof-producing
   Pancake decompiler ($CAKEMLDIR/pancake/decompiler) on qsort.pnk and print
   the theorems it produces.  See "Alternatives considered" in README.md.

   First build the decompiler:
     cd $CAKEMLDIR/pancake/decompiler && Holmake panItreeDecompilerLib.uo
   then, in hol/pancake (with the plain HOL heap, not the basis heap, whose
   CakeML type `v` clashes with Pancake's):
     hol < dev/decompile_try.sml *)
val _ = app load ["panPtreeConversionTheory", "panItreeDecompilerLib", "panItreeAbsSemTheory", "panContractLib"];
(* (not opened, to keep the output small) *) structure D = panItreeDecompilerLib;
val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.declare_monad("itree", {unit = “Ret”, bind = “itree_bind”, ignorebind = NONE,
                                choice = NONE, fail = NONE, guard = NONE});
val _ = monadsyntax.enable_monad "itree";
val (qs_topdecs, _) = panContractLib.parse_pancake_file "qsort.pnk";
val qs_fundecs = D.topdecs_to_fundecs qs_topdecs;
val _ = print "%%PARSED\n";
val t0 = Time.now ();
val qs_result = D.decompile_2_reduce “:64” "qsortDec" [] qs_fundecs;
val _ = print ("%%DECOMPILED in " ^ Time.toString (Time.- (Time.now (), t0)) ^ "s\n");
val _ = print "%%RESULTS\n";
val _ = Globals.max_print_depth := 30;
fun show i =
  let val (th, inner, defs) = List.nth (fst qs_result, i)
  in print ("\n%%FUNCTION " ^ Int.toString i ^ ": " ^ Int.toString (length inner) ^
            " loop theorems, " ^ Int.toString (length defs) ^ " definitions\n");
     print_thm th; print "\n";
     app (fn d => (print "\n-- definition:\n"; print_thm d; print "\n")) defs;
     app (fn d => (print "\n-- loop theorem:\n"; print_thm d; print "\n")) inner
  end;
val _ = List.app show [0, 1, 2, 3];
