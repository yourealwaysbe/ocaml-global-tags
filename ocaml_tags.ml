(* ocaml_tags.ml
 * Matthew Hague (matth1982@gmail.com)
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)





open Camlp4.Sig;;

(* identification module *)
module Id = struct
  (* name is printed with the -loaded-modules switch *)
  let name = "Ocaml global tagger plugin"
  (* cvs id's seem to be the preferred version string *)
  let version = "$Id: ocaml_tags.ml,v 1.6 2009/05/24 21:37:09 matth Exp $"
end


(* the real thing containing the real functions *)
module Make (Syntax : Camlp4.Sig.Camlp4Syntax) :
  Camlp4.Sig.Printer(Syntax.Ast).S =
struct
  include Syntax

  (* Because getting filename from Loc seems to corrupt in cases *)
  let orig_filename = ref ""

  let opt_string = function
    | None -> "<None>"
    | Some s -> s


  let get_end_of_path filename = 
    try
        (String.rindex filename '/') + 1
    with Not_found -> 0 
    
  let print_file_tag filename = 
    try
        let ext_pos = String.rindex filename '.' in
        let end_dir_pos = get_end_of_path filename in
        let name_len = (ext_pos - end_dir_pos) in
        let file_name = String.sub filename (end_dir_pos) name_len in 
        let mod_name_first = String.sub filename (end_dir_pos) 1 in
        let mod_name_rest = String.sub filename 
                                       (end_dir_pos + 1) 
                                       (name_len - 1) in
        let mod_name = (String.capitalize mod_name_first) ^ mod_name_rest in
        Printf.printf "%s\t%d\t%s\t%s\n" file_name 0 filename "Module file";
        Printf.printf "%s\t%d\t%s\t%s\n" mod_name 0 filename ("Module " ^ mod_name)
    with _ -> (* oh well, we tried *) ()

  let print_tag (tag, loc, line) = 
    Printf.printf "%s\t%d\t%s\t%s\n" 
                  tag 
                  (Loc.start_line loc) 
                  (*(Loc.file_name loc)*)
                  !orig_filename
                  line
    
  let make_tag tag loc line = (tag, loc, line)

  let mb_bool mb = 
    match mb with
      Ast.BTrue -> true
    | _ -> false

  let rec ident_tagname ident = 
    match ident with
      (* i . i  (keep last) *)
      Ast.IdAcc(loc, i1, i2) -> ident_tagname i2
      (* i i  (keep first) *)
    | Ast.IdApp(loc, i1, i2) -> ident_tagname i1
      (* foo *)
    | Ast.IdLid(loc, foo) ->  foo
      (* Bar *)
    | Ast.IdUid(loc, bar) -> bar 
      (* $s$ *)
    | Ast.IdAnt(loc, s) -> s


  let rec module_type_info ast = 
    match ast with
      (* functor (s : mt) -> mt *)
    | Ast.MtFun(loc, name, mt1, mt2) -> 
        List.append (module_type_info mt1) (module_type_info mt2)
      (* sig sg end *)
    | Ast.MtSig(loc, sig_item) -> sig_item_info sig_item
    | _ -> []

   and ctyp_info ast =
    match ast with
    | Ast.TyCls(loc, i(* #i *) (* #point *)) -> 
        let i_name = ident_tagname i in
        [make_tag i_name loc i_name]
    | Ast.TyId (loc, i(* i *) (* Lazy.t *)) -> 
        let i_name = ident_tagname i in
        [make_tag i_name loc i_name]
      (* type t 'a 'b 'c = t constraint t = t constraint t = t *)
    | Ast.TyDcl(loc, s, params, t2, contraint_pairs) -> [make_tag s loc s]
    | Ast.TyAnd(loc, t1, t2(* t and t *)) -> 
        List.append (ctyp_info t1) (ctyp_info t2)
    | Ast.TyOr (loc, t1, t2(* t | t *)) -> 
        List.append (ctyp_info t1) (ctyp_info t2)
    | Ast.TyPrv(loc, t(* private t *)) -> (ctyp_info t) 
    | Ast.TyMut(loc, t (* mutable t *)) -> (ctyp_info t)
    | _ -> []

  and module_binding_info ast =
    match ast with
      (* mb and mb *) (* module rec (s : mt) = me and (s : mt) = me *)
      Ast.MbAnd(loc, mb1, mb2) -> 
        List.append (module_binding_info mb1) (module_binding_info mb2)
      (* s : mt = me *)
    | Ast.MbColEq (loc, s, mt, me) -> 
        (make_tag s loc s)::(module_expr_info me)
      (* s : mt *)
    | Ast.MbCol (loc, s, mt) -> [make_tag s loc s]
    | _ -> []


  and rec_binding_info ast =
    match ast with
      (* rb ; rb *)
    | Ast.RbSem(loc, rb1, rb2) -> 
        List.append (rec_binding_info rb1) (rec_binding_info rb2)
      (* i = e *)
    | Ast.RbEq (loc, i, e) -> 
        let i_name = ident_tagname i in
        [make_tag i_name loc i_name]
    | _ -> []

  and patt_info ast =
    match ast with
      Ast.PaId (loc, i(* i *)) ->
        let i_tag = ident_tagname i in
        [make_tag i_tag loc i_tag]
    | Ast.PaAli(loc, p1, p2 (* p as p *) (* (Node x y as n) *)) -> (patt_info p2)
    | Ast.PaAnt(loc, s (* $s$ *)) ->  [make_tag s loc ("$" ^ s ^ "$")]
    | Ast.PaCom(loc, p1, p2(* p, p *)) -> 
        List.append (patt_info p1) (patt_info p2)
    | Ast.PaEq (loc, i, p(* i = p *)) -> 
        let i_name = ident_tagname i in
        (make_tag i_name loc i_name)::(patt_info p)
    | Ast.PaStr(loc, s(* s *)) -> [make_tag s loc s]
    | Ast.PaTup(loc, p(* ( p ) *)) -> patt_info p
    | Ast.PaTyc(loc, p, t(* (p : t) *)) -> patt_info p
    | Ast.PaTyp(loc, i (* #i *)) -> 
        let i_name = ident_tagname i in
        [make_tag i_name loc ("#" ^ i_name)]
    | _ -> []
    
  and sig_item_info ast = 
    match ast with
      (* class cict *)
    | Ast.SgCls(loc, cict) -> (class_type_info cict)
      (* class type cict *)
    | Ast.SgClt(loc, cict) -> (class_type_info cict)
      (* sg ; sg *)
    | Ast.SgSem(loc, sg1, sg2) ->
        List.append (sig_item_info sg1) (sig_item_info sg2)
      (* exception t *)
    | Ast.SgExc(loc, t) -> (ctyp_info t)
      (* module s : mt *)
    | Ast.SgMod(loc, s, mt) -> 
        (make_tag s loc ("module " ^ s))::(module_type_info mt)
      (* module rec mb *)
    | Ast.SgRecMod(loc, mb) -> (module_binding_info mb)
      (* module type s = mt *)
    | Ast.SgMty(loc, s, mt) -> 
        (make_tag s loc ("module type" ^ s))::(module_type_info mt)
      (* value s : t *)
    | Ast.SgVal(loc, s, t) -> [make_tag s loc ("value " ^ s)]
      (* type t *)
    | Ast.SgTyp(loc, t) -> (ctyp_info t)
    | _ -> []

  and module_expr_info ast = 
    match ast with
      (* me me *)
      Ast.MeApp(loc, me1, me2) -> 
        List.append (module_expr_info me1) (module_expr_info me2)
      (* functor (s : mt) -> me *)
    | Ast.MeFun(loc, s, mt, me) -> (module_expr_info me)
      (* struct st end *)
    | Ast.MeStr(loc, st) -> (str_item_info st)
      (* (me : mt) *)
    | Ast.MeTyc(loc, me, mt) -> 
        List.append (module_expr_info me) (module_type_info mt)
    | _ -> []

  and binding_info ast =
    match ast with
      Ast.BiNil(loc) -> []
      (* bi and bi *) (* let a = 42 and c = 43 *)
    | Ast.BiAnd(loc, bi1, bi2) -> List.append (binding_info bi1) (binding_info bi2)
      (* p = e *) (* let patt = expr *)
    | Ast.BiEq (loc, p, e) -> patt_info p 
      (* $s$ *)
    | Ast.BiAnt(loc, s) -> [make_tag s loc ("$" ^ s ^ "$")]


  and class_type_info ast =
    match ast with
      (* (virtual)? i ([ t ])? *)
    | Ast.CtCon(loc, mb, i, t) -> 
        let line = if (mb_bool mb) then "class virtual " else "class " in
        let i_name = ident_tagname i in
        [make_tag i_name loc (line ^ i_name)]
      (* [t] -> ct *)
    | Ast.CtFun(loc, t, ct) -> class_type_info ct
      (* object ((t))? (csg)? end *)
    | Ast.CtSig(loc, t, csg) -> class_sig_item_info csg
      (* ct and ct *)
    | Ast.CtAnd(loc, ct1, ct2) -> 
        List.append (class_type_info ct1) (class_type_info ct2)
      (* ct : ct *)
    | Ast.CtCol(loc, ct1, ct2) -> 
        List.append (class_type_info ct1) (class_type_info ct2)
      (* ct = ct *)
    | Ast.CtEq (loc, ct1, ct2) -> class_type_info ct1
    | _ -> []
  and class_sig_item_info ast =
    match ast with
      (* csg ; csg *)
    | Ast.CgSem(loc, csg1, csg2) -> 
        List.append (class_sig_item_info csg1) (class_sig_item_info csg2)
      (* method s : t or method private s : t *)
    | Ast.CgMth(loc, s, mb, t) -> 
        let line = if (mb_bool mb) then "method private " else "method " in
        [make_tag s loc (line ^ s)]
      (* value (virtual)? (mutable)? s : t *)
    | Ast.CgVal(loc, s, mb1, mb2, t) -> 
        let line1 = if (mb_bool mb1) then "virtual " else "" in
        let line2 = if (mb_bool mb2) then "mutable " else "" in
        [make_tag s loc (line1 ^ line2 ^ s)]
      (* method virtual (mutable)? s : t *)
    | Ast.CgVir(loc, s, mb, t) -> 
        let line = if (mb_bool mb) then "method virtual " else "method " in
        [make_tag s loc (line ^ s)]
    | _ -> []
  and class_str_item_info ast =
    match ast with
      (* cst ; cst *)
      Ast.CrSem(loc, cst1, cst2) -> 
        List.append (class_str_item_info cst1) (class_str_item_info cst2)
      (* method (private)? s : t = e or method (private)? s = e *)
    | Ast.CrMth(loc, s, mb, e, t) -> 
        let line = if (mb_bool mb) then "method private " else "method " in
        [make_tag s loc (line ^ s)]
      (* value (mutable)? s = e *)
    | Ast.CrVal(loc, s, mb, e) -> 
        let line = if (mb_bool mb) then "value mutable " else "value " in
        [make_tag s loc (line ^ s)]
      (* method virtual (private)? s : t *)
    | Ast.CrVir(loc, s, mb, t) -> 
        let line = if (mb_bool mb) then "method virtual private " else "method virtual " in
        [make_tag s loc (line ^ s)]
      (* value virtual (private)? s : t *)
    | Ast.CrVvr(loc, s, mb, t) -> 
        let line = if (mb_bool mb) then "value virtual private " else "value virtual " in
        [make_tag s loc (line ^ s)]
    | _ -> []

  and class_expr_info ast =
    match ast with
      (* ce e *)
      Ast.CeApp(loc, ce, e) -> class_expr_info ce 
      (* (virtual)? i ([ t ])? *)
    | Ast.CeCon(loc, mb, i, t) -> 
        let tag_name = ident_tagname i in
        let line = if (mb_bool mb) then "class virtual " else "class " in
        [make_tag tag_name loc (line ^ tag_name)]
      (* fun p -> ce *)
    | Ast.CeFun(loc, p, ce) -> (class_expr_info ce)
      (* let (rec)? bi in ce *)
    | Ast.CeLet(loc, mb, bi, ce) -> 
        List.append (binding_info bi) (class_expr_info ce)
      (* object ((p))? (cst)? end *)
    | Ast.CeStr(loc, p, cst) -> class_str_item_info cst
      (* ce : ct *)
    | Ast.CeTyc(loc, ce, ct) -> 
        List.append (class_expr_info ce) (class_type_info ct)
      (* ce and ce *)
    | Ast.CeAnd(loc, ce1, ce2) -> 
        List.append (class_expr_info ce1) (class_expr_info ce2)
      (* ce = ce *)
    | Ast.CeEq (loc, ce1, ce2) -> 
        List.append (class_expr_info ce1) (class_expr_info ce2)
    | _ -> []
    
  and str_item_info ast = 
    match ast with
      (* class cice *)
      Ast.StCls(loc, cice) -> class_expr_info cice
      (* class type cict *)
    | Ast.StClt(loc, cict) -> class_type_info cict
      (* st ; st *)
    | Ast.StSem(loc, st1, st2) -> 
        List.append (str_item_info st1) (str_item_info st2)
      (* exception t or exception t = i *)
    | Ast.StExc(loc, t, i) -> (ctyp_info t)
      (* e *)
    | Ast.StExp(loc, e) -> []
      (* module s = me *)
    | Ast.StMod(loc, s, me) -> 
        let tag = make_tag s loc ("module " ^ s) in
        tag::(module_expr_info me)
      (* module rec mb *)
    | Ast.StRecMod(loc, mb) -> (module_binding_info mb)
      (* module type s = mt *)
    | Ast.StMty(loc, s, mt) -> 
        (make_tag s loc ("module " ^ s))::(module_type_info mt)
      (* value (rec)? bi *)
    | Ast.StVal(loc, mb, bi) -> (binding_info bi)
      (* type t *)
    | Ast.StTyp(loc, t) -> (ctyp_info t)
    | _ -> []

  (* print_interf shall be called on .mli files *)
  let print_interf ?input_file ?output_file ast =
    orig_filename := opt_string input_file;
    let tags = sig_item_info ast in
    print_file_tag (opt_string input_file);
    List.iter print_tag tags


  (* print_implem shall be called on .ml files *)
  let print_implem ?input_file ?output_file ast =
    orig_filename := opt_string input_file;
    let tags = str_item_info ast in
    print_file_tag (opt_string input_file);
    List.iter print_tag tags

      
end

(* apply everything to register the new printer *)
module M = Camlp4.Register.OCamlPrinter(Id)(Make)

(* end of source *)

