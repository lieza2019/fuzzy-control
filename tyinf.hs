{- syntax definitions
   unary_operation := ++ int_var | -- int_var | - int_real_var
   
   func_declaration := fun FUNC-ID ({ARG-DECLS}) {as FUNC_TYPE} { FUNC_BODY }
   ARG-DECLS := VAL-DECL
   FUNC_TYPE := bool | int | etc.
   
   bin_ope := bin_ope1 | /
   bin_ope1 := - | + | *

   Gamma |- expr1 : t => Gamma |- ( expr1 ) : t
   
   (Gamma1 |- expr1 : int), (Gamma2 |- expr2 : int) => Gamma1 + Gamma2 |- expr1 bin-ope1 expr2 : int
   (Gamma1 |- expr1 : int), (Gamma2 |- expr2 : real) => Gamma1 + Gamma2 |- expr1 bin-ope1 expr2 : real
   (Gamma1 |- expr1 : real), (Gamma2 |- expr2 : int) => Gamma1 + Gamma2 |- expr1 bin-ope1 expr2 : real
   (Gamma1 |- expr1 : real), (Gamma2 |- expr2 : real) => Gamma1 + Gamma2 |- expr1 bin-ope1 expr2 : real
   
   Gamma |- x : int => Gamma |- -- x : int
   Gamma |- x : int => Gamma |- ++ x : int
   
   Gamma |- x : int => Gamma |- - x : int
   Gamma |- x : real => Gamma |- - x : real
-}

--import Text.Parsec.Char
--import Text.Parsec.Prim
--import Text.Parsec.String

import Data.Map as M
import Data.Set as Set
import Control.Exception as Except
import Control.Monad.State as St
import Control.Exception (assert)
import Debug.Trace as Dbg
import System.IO


ras_trace str expr =
  let suppress = True
  in
    if not suppress then (Dbg.trace str expr) else expr

halt :: Error_codes -> IO ()
halt err = do
  putStrLn $ show err
  return $ assert False ()


data Sym_category =
  Sym_cat_typedef
  | Sym_cat_record
  | Sym_cat_func
  | Sym_cat_decl
  deriving (Eq, Ord, Show)

type Row = Integer
type Col = Integer
data Sym_attrib =
  Sym_attrib {sym_attr_geometry :: (Row, Col), sym_attr_entity ::  Syntree_node}
  deriving (Eq, Ord, Show)

data Symtbl_node =
  Sym_entry {sym_ident :: String, sym_attr :: Sym_attrib}
  deriving (Eq, Ord, Show)

data Symtbl_cluster =
  Sym_empty
  | Sym_add Symtbl_node Symtbl_cluster
  deriving (Eq, Ord, Show)

data Symtbl_anon_ident =
  Symtbl_anon_ident {sym_anon_var :: Integer, sym_anon_record :: Integer}
  deriving (Eq, Ord, Show)

type Scope_Lvl = Integer
data Sym_tbl =
  Scope_empty
  | Scope_add (Scope_Lvl, Symtbl_anon_ident, Symtbl_cluster) Sym_tbl
  deriving (Eq, Ord, Show)

data Symtbl =
  Symtbl {sym_typedef :: Sym_tbl, sym_record :: Sym_tbl, sym_func :: Sym_tbl, sym_decl :: Sym_tbl}
  deriving (Eq, Ord, Show)

sym_categorize :: Symtbl -> Sym_category -> Sym_tbl
sym_categorize symtbl cat =
  ras_trace "in sym_categorize" (
  case cat of
    Sym_cat_typedef -> sym_typedef symtbl
    Sym_cat_record -> sym_record symtbl
    Sym_cat_func -> sym_func symtbl
    Sym_cat_decl -> sym_decl symtbl
  )


sym_update :: Symtbl -> Sym_category ->Sym_tbl -> Symtbl
sym_update symtbl cat tbl =
  ras_trace "in sym_update" (
  case cat of
    Sym_cat_typedef -> symtbl{sym_typedef = tbl}
    Sym_cat_func -> symtbl{sym_func = tbl}
    Sym_cat_record -> symtbl{sym_record = tbl}
    Sym_cat_decl -> symtbl{sym_decl = tbl}
  )


sym_leave_scope :: Symtbl -> Sym_category -> Symtbl
sym_leave_scope symtbl cat =
  ras_trace "in sym_leave_scope" (
  let sym_tbl = sym_categorize symtbl cat
  in
    let sym_tbl' = case sym_tbl of
                     Scope_empty -> Scope_empty
                     Scope_add sco sym_tbl' -> sym_tbl'
    in
      sym_update symtbl cat sym_tbl'
  )

sym_enter_scope :: Maybe Symtbl -> Sym_category -> Symtbl
sym_enter_scope symtbl cat =
  ras_trace "in sym_enter_scope" (
  case symtbl of
    Just s_tbl -> let sym_tbl = sym_categorize s_tbl cat      
                  in
                    let sym_tbl' = case sym_tbl of
                                     Scope_empty -> Scope_add (0, Symtbl_anon_ident {sym_anon_var = 1, sym_anon_record = 1}, Sym_empty) Scope_empty
                                     Scope_add (lv, sym_anon_ident, _) _ -> Scope_add (lv + 1, sym_anon_ident, Sym_empty) sym_tbl
                    in
                      sym_update s_tbl cat sym_tbl'
    Nothing -> Symtbl {sym_typedef = Scope_empty, sym_record = Scope_empty, sym_func = Scope_empty, sym_decl = Scope_empty}
  )


sym_new_anonid_var :: Symtbl -> Sym_category -> (String, String, String) -> (String, Symtbl)
sym_new_anonid_var symtbl cat (prfx, sfix, sep) =
  ras_trace "in sym_new_anonid_var" (
  let d2s_var m = "var_" ++ ((prfx ++ sep) ++ (show m) ++ (sep ++ sfix))
      sym_tbl = sym_categorize symtbl cat
  in
    let sym_tbl' = (case sym_tbl of
                      Scope_empty -> sym_categorize (sym_enter_scope (Just symtbl) cat) cat
                      Scope_add _ _ -> sym_tbl
                   )
    in
      let r = case sym_tbl' of
                Scope_add (lv, anon_crnt@(Symtbl_anon_ident {sym_anon_var = crnt_top}), syms) sym_tbls' ->
                  ((d2s_var crnt_top), Scope_add (lv, anon_crnt {sym_anon_var = crnt_top + 1}, syms) sym_tbls')
      in
        case r of
          (anonid, sym_tbl'') -> (anonid, sym_update symtbl cat sym_tbl'')
  )

sym_new_anonid_rec :: Symtbl -> Sym_category -> (String, String, String) -> (String, Symtbl)
sym_new_anonid_rec symtbl cat (prfx, sfix, sep) =
  ras_trace "in sym_new_anonid_rec" (
  let d2s_rec m = "rec_" ++ ((prfx ++ sep) ++ (show m) ++ (sep ++ sfix))
      sym_tbl = sym_categorize symtbl cat
  in
    let sym_tbl' = (case sym_tbl of
                      Scope_empty -> sym_categorize (sym_enter_scope (Just symtbl) cat) cat
                      Scope_add _ _ -> sym_tbl
                   )
    in
      let r = case sym_tbl' of
                Scope_add (lv, anon_crnt@(Symtbl_anon_ident {sym_anon_record = crnt_top}), syms) sym_tbls' ->
                  ((d2s_rec crnt_top), Scope_add (lv, anon_crnt {sym_anon_record = crnt_top + 1}, syms) sym_tbls')
      in
        case r of
          (anonid, sym_tbl'') -> (anonid, sym_update symtbl cat sym_tbl'')
  )


sym_search :: Symtbl -> Sym_category -> String -> Maybe (Sym_attrib, Symtbl)
sym_search symtbl cat ident =
  ras_trace "in sym_search" (
  let walk syms ident =
        case syms of
          Sym_empty -> Nothing
          Sym_add sym syms' -> if ((sym_ident sym) == ident) then Just (sym, ((Sym_add sym Sym_empty), syms'))
                               else case (walk syms' ident) of
                                      Nothing -> Nothing
                                      Just (found, (pasts, remainders)) -> Just (found, ((Sym_add sym pasts), remainders))
      sym_tbl = sym_categorize symtbl cat
  in
    case sym_tbl of
      Scope_empty -> Nothing
      Scope_add (lv, anon_idents, syms) sym_tbl' -> (case (walk syms ident) of
                                                       Just (found, (pasts,remainders)) -> Just ((sym_attr found), symtbl')
                                                         where
                                                           symtbl' = sym_update symtbl cat $ Scope_add (lv, anon_idents, remainders) sym_tbl'
                                                       Nothing -> sym_search (sym_update symtbl cat sym_tbl') cat ident
                                                    )
  )


sym_lkup_tydef_decl :: Symtbl -> String -> Maybe (Sym_attrib, Symtbl)
sym_lkup_tydef_decl symtbl ident =
  ras_trace "in sym_lkup_tydef_decl" (
  case sym_search symtbl Sym_cat_typedef ident of
    Just r@(attr, symtbl') -> (case sym_attr_entity attr of
                                 Syn_tydef_decl _ _ -> Just r
                                 _ -> sym_lkup_tydef_decl symtbl' ident
                              )
    Nothing -> Nothing
  )

sym_lkup_fun_decl :: Symtbl -> String -> Maybe (Sym_attrib, Symtbl)
sym_lkup_fun_decl symtbl ident =
  ras_trace "in sym_lkup_fun_decl" (
  case sym_search symtbl Sym_cat_decl ident of
    Just r@(attr, symtbl') -> (case sym_attr_entity attr of
                                 Syn_fun_decl _ _ _ _ -> Just r
                                 _ -> sym_lkup_fun_decl symtbl' ident
                              )
    Nothing -> (case sym_search symtbl Sym_cat_func ident of
                  Just r'@(attr', symtbl'') -> (case sym_attr_entity attr' of
                                                 Syn_fun_decl _ _ _ _ -> Just r'
                                                 _ -> sym_lkup_fun_decl symtbl'' ident
                                              )
                  Nothing -> Nothing
               )
  )

sym_lkup_rec_decl :: Symtbl -> String -> Maybe (Sym_attrib, Symtbl)
sym_lkup_rec_decl symtbl ident =
  ras_trace "in sym_lkup_rec_decl" (
  case sym_search symtbl Sym_cat_record ident of
    Just r@(attr, symtbl') -> (case sym_attr_entity attr of
                                 Syn_rec_decl _ _ -> Just r
                                 _ -> sym_lkup_rec_decl symtbl' ident
                              )
    Nothing -> Nothing
  )

sym_lkup_var_decl :: Symtbl -> String -> Maybe (Sym_attrib, Symtbl)
sym_lkup_var_decl symtbl ident =
  ras_trace "in sym_lkup_var_decl" (
  case sym_search symtbl Sym_cat_decl ident of
    Just r@(attr, symtbl') -> (case sym_attr_entity attr of
                                 Syn_var_decl _ _ -> Just r
                                 _ -> sym_lkup_var_decl symtbl' ident
                              )
    Nothing -> Nothing
  )


walk_on_scope :: Symtbl_cluster -> (String, Syntree_node) -> Maybe Symtbl_node
walk_on_scope sym_cluster (ident, entity) =
  ras_trace "in walk_on_scope" (
  let cmp_entity (Sym_entry {sym_attr = attr}) =
        case (sym_attr_entity attr) of
          Syn_tydef_decl _ _ -> (case entity of
                               Syn_tydef_decl _ _ -> True
                               _ -> False
                            )
          Syn_fun_decl _ _ _ _ -> (case entity of
                                     Syn_fun_decl _ _ _ _ -> True
                                     _ -> False
                                  )
          Syn_rec_decl _ _ -> (case entity of
                             Syn_rec_decl _ _ -> True
                             _ -> False
                          )
          Syn_var_decl _ _ -> (case entity of
                                 Syn_var_decl _ _ -> True
                                 _ -> False
                              )
          _ -> False
  in
    case sym_cluster of
      Sym_add sym syms -> if ((cmp_entity sym) && ((sym_ident sym) == ident)) then Just sym
                          else walk_on_scope syms (ident, entity)
      Sym_empty -> Nothing
  )


{-
sym_regist :: Bool -> Symtbl -> Sym_category -> Syntree_node -> (Symtbl, Maybe Error_codes)
sym_regist ovwt symtbl cat entity =
  ras_trace "in sym_regist" (
  let reg_sym sym_tbl (ident, sym) =
        case sym_tbl of
          Scope_empty -> ((Scope_add (0, Symtbl_anon_ident {sym_anon_var = 1, sym_anon_record = 1}, (Sym_add sym Sym_empty)) Scope_empty), Nothing)            
          Scope_add (lv, anon_idents, syms) sym_tbls -> (case syms of
                                                           Sym_empty -> ((Scope_add (lv, anon_idents, (Sym_add sym Sym_empty)) sym_tbls), Nothing)
                                                           Sym_add s_node _ -> (case walk_on_scope syms (ident, (sym_attr_entity . sym_attr) s_node) of
                                                                                  Just e -> if (not ovwt) then (sym_tbl, Just Symbol_redifinition)
                                                                                            else ((Scope_add (lv, anon_idents, (Sym_add sym syms)) sym_tbls), Nothing)
                                                                                  Nothing -> ((Scope_add (lv, anon_idents, (Sym_add sym syms)) sym_tbls), Nothing)
                                                                               )
                                                        )
      sym_tbl = sym_categorize symtbl cat
  in
    let (sym_tbl', err) = case entity of
          Syn_tydef_decl ty_id _ -> reg_sym sym_tbl (ty_id, Sym_entry {sym_ident = ty_id, sym_attr = Sym_attrib {sym_attr_geometry = (-1, -1), sym_attr_entity = entity}})
          Syn_fun_decl fun_id _ _ _ -> reg_sym sym_tbl (fun_id, Sym_entry {sym_ident = fun_id, sym_attr = Sym_attrib {sym_attr_geometry = (-1, -1), sym_attr_entity = entity}})
          Syn_rec_decl rec_id _ -> reg_sym sym_tbl (rec_id, Sym_entry {sym_ident = rec_id, sym_attr = Sym_attrib {sym_attr_geometry = (-1, -1), sym_attr_entity = entity}})
          Syn_var_decl var_id _ -> reg_sym sym_tbl (var_id, Sym_entry {sym_ident = var_id, sym_attr = Sym_attrib {sym_attr_geometry = (-1, -1), sym_attr_entity = entity}})
    in
      ((sym_update symtbl cat sym_tbl'), err)
  ) -}

sym_regist :: Bool -> Symtbl -> Sym_category -> (String, Syntree_node) -> (Symtbl, Maybe Error_codes)
sym_regist ovwt symtbl cat (ident, entity) =
  ras_trace "in sym_regist" (
  let reg_sym sym_tbl (ident, sym) =
        case sym_tbl of
          Scope_empty -> ((Scope_add (0, Symtbl_anon_ident {sym_anon_var = 1, sym_anon_record = 1}, (Sym_add sym Sym_empty)) Scope_empty), Nothing)            
          Scope_add (lv, anon_idents, syms) sym_tbls -> (case syms of
                                                           Sym_empty -> ((Scope_add (lv, anon_idents, (Sym_add sym Sym_empty)) sym_tbls), Nothing)
                                                           Sym_add s_node _ -> (case walk_on_scope syms (ident, (sym_attr_entity . sym_attr) s_node) of
                                                                                  Just e -> if (not ovwt) then (sym_tbl, Just Symbol_redifinition)
                                                                                            else ((Scope_add (lv, anon_idents, (Sym_add sym syms)) sym_tbls), Nothing)
                                                                                  Nothing -> ((Scope_add (lv, anon_idents, (Sym_add sym syms)) sym_tbls), Nothing)
                                                                               )
                                                        )
      sym_tbl = sym_categorize symtbl cat
  in
    let (sym_tbl', err) = reg_sym sym_tbl (ident, Sym_entry {sym_ident = ident, sym_attr = Sym_attrib {sym_attr_geometry = (-1, -1), sym_attr_entity = entity}})
    in
      ((sym_update symtbl cat sym_tbl'), err)
  )


data Expr =
  Var String
  | Numeric Integer
  | App Expr Expr
  | Fun String Expr
  deriving (Show, Eq)


data Tk_code =
  Tk_nonsense
  | Tk_nume Integer
  | Tk_str String
  | Tk_typed_as
  | Tk_var
  | Tk_if
  | Tk_then
  | Tk_else
  | Tk_decre
  | Tk_incre
  | Tk_slash
  | Tk_star
  | Tk_shaft
  | Tk_cross
  | Tk_asgn
  | Tk_equ
  | Tk_smcl
  | Tk_L_bra
  | Tk_L_par
  | Tk_R_bra
  | Tk_R_par
  | Tk_fun
  | Tk_bool
  | Tk_int
  | Tk_true
  | Tk_false
  | Tk_ident String
  deriving (Eq, Ord, Show)

data Quo_stat =
  No_quoted String
  | Single_quoted Char
  | Double_quoted String
  deriving (Eq, Ord, Show)

data Par_stat =
  Par_ini
  | Par_asgn_1
  | Par_equ_1
  -- | Par_L_par
  -- | Par_R_par
  | Par_str
  | Par_nume Integer
  | Par_keyword_as_1
  | Par_keyword_bool_1
  | Par_keyword_bool_2
  | Par_keyword_bool_3
  | Par_keyword_decre_1
  | Par_keyword_else_1
  | Par_keyword_else_2
  | Par_keyword_else_3
  | Par_keyword_fun_false_1
  | Par_keyword_fun_2
  | Par_keyword_false_2
  | Par_keyword_false_3
  | Par_keyword_false_4
  | Par_keyword_if_int_1
  | Par_keyword_int_2
  | Par_keyword_incre_1
  | Par_keyword_then_true_1
  | Par_keyword_then_2
  | Par_keyword_then_3
  | Par_keyword_true_2
  | Par_keyword_true_3
  | Par_acc Tk_code
  | Par_err
  deriving (Eq, Ord, Show)


is_blank c = ((c == ' ') || (c == '\t'))

is_delim c =
  case c of
    ' ' -> True
    '\t' -> True
    '=' -> True
    '>' -> True
    '{' -> True
    '(' -> True
    '}' -> True
    ')' -> True
    '/' -> True
    '*' -> True
    '-' -> True
    '+' -> True
    '"' -> True
    ';' -> True
    ':' -> True
    _ -> False

is_digit c =
  case c of
    '1' -> Just 1
    '2' -> Just 2
    '3' -> Just 3
    '4' -> Just 4
    '5' -> Just 5
    '6' -> Just 6
    '7' -> Just 7
    '8' -> Just 8
    '9' -> Just 9
    '0' -> Just 0
    _ -> Nothing

is_alpha c =
  Set.member c alps
  where
    alps = Set.fromList ['a'..'z']

is_alnum c =
  case (is_digit c) of
    Nothing -> is_alpha c
    Just _ -> True


parse_mata :: St.State ((Par_stat, Maybe Quo_stat), String) ()
parse_mata = do
  ((par_stat, quo_stat), src) <- St.get
  case par_stat of
    Par_err -> St.put ((par_stat, quo_stat), src)
    _ -> St.modify state_trans
      where
        state_trans (crnt_stat@(par_stat, quo_stat), "") =
          case par_stat of
            Par_ini -> ((Par_acc Tk_nonsense, quo_stat), "")
            Par_str -> (case quo_stat of
                          Just (No_quoted str) -> ((Par_acc (Tk_ident str), Nothing), "")
                          _ -> ((Par_err, quo_stat), "")
                       )
            Par_asgn_1 -> ((Par_err, quo_stat), "")
            Par_equ_1 -> ((Par_err, quo_stat), "")
            _ -> (crnt_stat, "")
            
        state_trans (stat@(par_stat, quo_stat), src@(c:cs)) =
          case par_stat of
            Par_ini | (c == 'a') -> ((Par_keyword_as_1, quo_stat), cs)
            Par_ini | (c == 'b') -> ((Par_keyword_bool_1, quo_stat), cs)
            Par_ini | (c == 'e') -> ((Par_keyword_else_1, quo_stat), cs)
            Par_ini | (c == 'f') -> ((Par_keyword_fun_false_1, quo_stat), cs)
            Par_ini | (c == 'i') -> ((Par_keyword_if_int_1, quo_stat), cs)
            Par_ini | (c == 't') -> ((Par_keyword_then_true_1, quo_stat), cs)
            Par_ini | (is_delim c) -> if (is_blank c) then (stat, cs)
                                      else case par_delim_chr c quo_stat of
                                             (Par_err, quo_stat') -> ((Par_err, quo_stat'), src)
                                             (par_stat', quo_stat') -> ((par_stat', quo_stat'), cs)
            Par_ini -> (case (is_digit c) of
                          Just n -> ((Par_nume n, quo_stat), cs)
                          Nothing -> if (is_alnum c) then
                                       ((Par_str, Just (No_quoted [c])), cs)
                                     else
                                       ((Par_err, quo_stat), src)
                       )

            Par_asgn_1 | (c == '=') -> ((Par_acc Tk_asgn, quo_stat), cs)
            Par_equ_1 | (c == '=') -> ((Par_acc Tk_equ, quo_stat), cs)
            
            Par_str -> (case quo_stat of
                          Just (No_quoted str) -> if (is_alnum c) then ((Par_str, Just (No_quoted (str ++ [c]))), cs)
                                                  else ((Par_acc (Tk_ident str), Nothing), src)
                          Just (Double_quoted str) -> if (c == '"') then ((Par_acc (Tk_str str), Nothing), cs)
                                                      else ((Par_str, Just (Double_quoted (str ++ [c]))), cs)
                          _ -> ((Par_err, quo_stat), src)
                       )
            Par_nume m -> (case (is_digit c) of
                             Just n -> ((Par_nume (m * 10 + n), quo_stat), cs)
                             Nothing -> ((Par_acc (Tk_nume m), quo_stat), src)
                          )
            Par_keyword_decre_1 | (c == '-') -> ((Par_acc Tk_decre, quo_stat), cs)
            Par_keyword_decre_1 -> ((Par_acc Tk_shaft, quo_stat), src)
            Par_keyword_incre_1 | (c == '+') -> ((Par_acc Tk_incre, quo_stat), cs)
            Par_keyword_incre_1 -> ((Par_acc Tk_cross, quo_stat), src)
            Par_keyword_as_1 | (c == 's') -> (case cs of
                                                 [] -> ((Par_acc Tk_typed_as, quo_stat), "")
                                                 c':cs' | (is_delim c') -> ((Par_acc Tk_typed_as, quo_stat), cs)
                                                 _ -> ((Par_str, Just (No_quoted "as")), cs)
                                              )
            Par_keyword_as_1 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("a" ++ [c]))), cs)
                                else ((Par_acc (Tk_ident "a"), Nothing), src)
            
            Par_keyword_else_1 | (c == 'l') -> ((Par_keyword_else_2, quo_stat), cs)
            Par_keyword_else_1 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("e" ++ [c]))), cs)
                                  else ((Par_acc (Tk_ident "e"), Nothing), src)
            Par_keyword_else_2 | (c == 's') -> ((Par_keyword_else_3, quo_stat), cs)
            Par_keyword_else_2 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("el" ++ [c]))), cs)
                                  else ((Par_acc (Tk_ident "el"), Nothing), src)
            Par_keyword_else_3 | (c == 'e') -> (case cs of
                                                  [] -> ((Par_acc Tk_else, quo_stat), "")
                                                  c':cs' | (is_delim c') -> ((Par_acc Tk_else, quo_stat), cs)
                                                  _ -> ((Par_str, Just (No_quoted "else")), cs)
                                               )
            Par_keyword_else_3 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("els" ++ [c]))), cs)
                                  else ((Par_acc (Tk_ident "els"), Nothing), src)
            
            Par_keyword_fun_false_1 | (c == 'u') -> ((Par_keyword_fun_2, quo_stat), cs)
            Par_keyword_fun_false_1 | (c == 'a') -> ((Par_keyword_false_2, quo_stat), cs)
            Par_keyword_fun_false_1 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("f" ++ [c]))), cs)
                                       else ((Par_acc (Tk_ident "f"), Nothing), src)
            Par_keyword_fun_2 | (c == 'n') -> (case cs of
                                                 [] -> ((Par_acc Tk_fun, quo_stat), "")
                                                 c':cs' | (is_delim c') -> ((Par_acc Tk_fun, quo_stat), cs)
                                                 _ -> ((Par_str, Just (No_quoted "fun")), cs)
                                              )
            Par_keyword_fun_2 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("fu" ++ [c]))), cs)
                                 else ((Par_acc (Tk_ident "fu"), Nothing), src)
            
            Par_keyword_if_int_1 | (c == 'f') -> (case cs of
                                                    [] -> ((Par_acc Tk_if, quo_stat), "")
                                                    c':cs' | (is_delim c') -> ((Par_acc Tk_if, quo_stat), cs)
                                                    _ -> ((Par_str, Just (No_quoted "if")), cs)
                                                 )
            Par_keyword_if_int_1 | (c == 'n') -> ((Par_keyword_int_2, quo_stat), cs)
            Par_keyword_if_int_1 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("i" ++ [c]))), cs)
                                    else ((Par_acc (Tk_ident "i"), Nothing), src)
            Par_keyword_int_2 | (c == 't') -> (case cs of
                                                 [] -> ((Par_acc Tk_int, quo_stat), "")
                                                 c':cs' | (is_delim c') -> ((Par_acc Tk_int, quo_stat), cs)
                                                 _ -> ((Par_str, Just (No_quoted "int")), cs)
                                              )
            Par_keyword_int_2 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("in" ++ [c]))), cs)
                                 else ((Par_acc (Tk_ident "in"), Nothing), src)
            
            Par_keyword_bool_1 | (c == 'o') -> ((Par_keyword_bool_2, quo_stat), cs)
            Par_keyword_bool_1 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("b" ++ [c]))), cs)
                                  else ((Par_acc (Tk_ident "b"), Nothing), src)
            Par_keyword_bool_2 | (c == 'o') -> ((Par_keyword_bool_3, quo_stat), cs)
            Par_keyword_bool_2 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("bo" ++ [c]))), cs)
                                  else ((Par_acc (Tk_ident "bo"), Nothing), src)
            Par_keyword_bool_3 | (c == 'l') -> (case cs of
                                                  [] -> ((Par_acc Tk_bool, quo_stat), "")
                                                  c':cs' | (is_delim c') -> ((Par_acc Tk_bool, quo_stat), cs)
                                                  _ -> ((Par_str, Just (No_quoted "bool")), cs)
                                               )
            Par_keyword_bool_3 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("boo" ++ [c]))), cs)
                                  else ((Par_acc (Tk_ident "boo"), Nothing), src)
            
            Par_keyword_then_true_1 | (c == 'h') -> ((Par_keyword_then_2, quo_stat), cs)
            Par_keyword_then_true_1 | (c == 'r') -> ((Par_keyword_true_2, quo_stat), cs)
            Par_keyword_then_true_1 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("t" ++ [c]))), cs)
                                       else ((Par_acc (Tk_ident "t"), Nothing), src)
            Par_keyword_then_2 | (c == 'e') -> ((Par_keyword_then_3, quo_stat), cs)
            Par_keyword_then_2 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("th" ++ [c]))), cs)
                                  else ((Par_acc (Tk_ident "th"), Nothing), src)
            Par_keyword_then_3 | (c == 'n') -> (case cs of
                                                  [] -> ((Par_acc Tk_then, quo_stat), "")
                                                  c':cs' | (is_delim c') -> ((Par_acc Tk_then, quo_stat), cs)
                                                  _ -> ((Par_str, Just (No_quoted "then")), cs)
                                               )
            Par_keyword_then_3 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("the" ++ [c]))), cs)
                                  else ((Par_acc (Tk_ident "the"), Nothing), src)
            Par_keyword_true_2 | (c == 'u') -> ((Par_keyword_true_3, quo_stat), cs)
            Par_keyword_true_2 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("tr" ++ [c]))), cs)
                                  else ((Par_acc (Tk_ident "tr"), Nothing), src)
            Par_keyword_true_3 | (c == 'e') -> (case cs of
                                                  [] -> ((Par_acc Tk_true, quo_stat), "")
                                                  c':cs' | (is_delim c') -> ((Par_acc Tk_true, quo_stat), cs)
                                                  _ -> ((Par_str, Just (No_quoted "true")), cs)
                                               )
            Par_keyword_true_3 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("tru" ++ [c]))), cs)
                                  else ((Par_acc (Tk_ident "tru"), Nothing), src)
            
            Par_keyword_false_2 | (c == 'l') -> ((Par_keyword_false_3, quo_stat), cs)
            Par_keyword_false_2 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("fa" ++ [c]))), cs)
                                   else ((Par_acc (Tk_ident "fa"), Nothing), src)
            Par_keyword_false_3 | (c == 's') -> ((Par_keyword_false_4, quo_stat), cs)
            Par_keyword_false_3 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("fal" ++ [c]))), cs)
                                  else ((Par_acc (Tk_ident "fal"), Nothing), src)
            Par_keyword_false_4 | (c == 'e') -> (case cs of
                                                  [] -> ((Par_acc Tk_false, quo_stat), "")
                                                  c':cs' | (is_delim c') -> ((Par_acc Tk_false, quo_stat), cs)
                                                  _ -> ((Par_str, Just (No_quoted "false")), cs)
                                               )
            Par_keyword_false_4 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("fals" ++ [c]))), cs)
                                  else ((Par_acc (Tk_ident "fals"), Nothing), src)
            
            Par_acc (Tk_nume _) -> ((Par_ini, quo_stat), src)
            Par_acc _ -> if (is_delim c) then
                           (if (is_blank c) then ((Par_ini, quo_stat), cs)
                            else case par_delim_chr c quo_stat of                            
                                   (Par_err, quo_stat') -> ((Par_err, quo_stat'), src)
                                   (par_stat', quo_stat') -> ((par_stat', quo_stat'), cs)
                           )
                         else ((Par_ini, quo_stat), src)
            _ -> ((Par_err, quo_stat), src)
          
          where
            par_delim_chr c crnt_quo_stat =
              case c of
                '=' -> (Par_equ_1, crnt_quo_stat)
                '{' -> (Par_acc Tk_L_bra, crnt_quo_stat)
                '(' -> (Par_acc Tk_L_par, crnt_quo_stat)
                '}' -> (Par_acc Tk_R_bra, crnt_quo_stat)
                ')' -> (Par_acc Tk_R_par, crnt_quo_stat)
                '/' -> (Par_acc Tk_slash, crnt_quo_stat)
                '*' -> (Par_acc Tk_star, crnt_quo_stat)
                '-' -> (Par_keyword_decre_1, crnt_quo_stat)
                '+' -> (Par_keyword_incre_1, crnt_quo_stat)
                '"' -> (Par_str, Just (Double_quoted ""))
                ';' -> (Par_acc Tk_smcl, crnt_quo_stat)
                ':' -> (Par_asgn_1, crnt_quo_stat)
                _ -> (Par_err, crnt_quo_stat)


parse_exec :: (Par_stat, Maybe Quo_stat) -> String -> (([Par_stat], Maybe Quo_stat), String)
parse_exec stat@(par_stat, quo_stat) src =
  if (src == "") then
    case par_stat of
      Par_ini -> (([Par_acc Tk_nonsense], quo_stat), "")
      Par_nume n -> (([Par_acc (Tk_nume n)], quo_stat), "")
      Par_str -> (case quo_stat of
                    Just (No_quoted str) -> (([Par_acc (Tk_ident str)], quo_stat), "")
                    _ -> (([Par_err], quo_stat), "")
                 )
      Par_keyword_as_1 -> (([Par_acc (Tk_ident "a")], quo_stat), "")
      Par_keyword_fun_false_1 -> (([Par_acc (Tk_ident "f")], quo_stat), "")
      Par_keyword_fun_2 -> (([Par_acc (Tk_ident "fu")], quo_stat), "")
      Par_keyword_false_2 -> (([Par_acc (Tk_ident "fa")], quo_stat), "")
      Par_keyword_false_3 -> (([Par_acc (Tk_ident "fal")], quo_stat), "")
      Par_keyword_false_4 -> (([Par_acc (Tk_ident "fals")], quo_stat), "")
      Par_keyword_bool_1 -> (([Par_acc (Tk_ident "b")], quo_stat), "")
      Par_keyword_bool_2 -> (([Par_acc (Tk_ident "bo")], quo_stat), "")
      Par_keyword_bool_3 -> (([Par_acc (Tk_ident "boo")], quo_stat), "")
      Par_keyword_if_int_1 -> (([Par_acc (Tk_ident "i")], quo_stat), "")
      Par_keyword_int_2 -> (([Par_acc (Tk_ident "in")], quo_stat), "")
      Par_keyword_then_true_1 -> (([Par_acc (Tk_ident "t")], quo_stat), "")
      Par_keyword_then_2 -> (([Par_acc (Tk_ident "th")], quo_stat), "")
      Par_keyword_then_3 -> (([Par_acc (Tk_ident "the")], quo_stat), "")
      Par_keyword_true_2 -> (([Par_acc (Tk_ident "tr")], quo_stat), "")
      Par_keyword_true_3 -> (([Par_acc (Tk_ident "tru")], quo_stat), "")
      Par_acc _ -> (([], quo_stat), "")
      _ -> (([], quo_stat), "")
  else
    case stat of
      (Par_err, quo_stat) -> (([Par_err], quo_stat), src)
      _ -> let (_, (stat'@(par_stat', _), src')) = St.runState parse_mata (stat, src)
               ((tokens, quo_stat''), src'') = (parse_exec stat' src')
           in
             let tokens' = (case par_stat' of
                              Par_acc tk -> [par_stat']
                              _ -> []
                           ) ++ tokens
             in
               ((tokens', quo_stat''), src'')

conv2_tokens :: String -> ([Tk_code], String)
conv2_tokens src =
  let ((tokens, _), src') = parse_exec (Par_ini, Nothing) src
  in
    (concatMap (\tk -> case tk of
                         Par_acc tk' -> if tk' == Tk_nonsense then [] else [tk']
                         Par_err -> []
               ) tokens,
     src')


data Type =
  Ty_top
  | Ty_bool
  | Ty_string
  | Ty_int
  | Ty_var String
  | Ty_pair (Type, Type)
  -- | Ty_fun (Type, Type)
  | Ty_fun [Type]
  | Ty_abs
  | Ty_btm
  | Ty_unknown
  deriving (Eq, Ord, Show)

data Operation =
  Ope_asgn
  | Ope_decre
  | Ope_incre
  | Ope_neg
  | Ope_add
  | Ope_sub
  | Ope_mul
  | Ope_div
  deriving (Eq, Ord, Show)

data Val =
  Val_str String
  | Val_bool Bool
  | Val_int Integer
  deriving (Eq, Ord, Show)

data Syntree_node =
  Syn_ty_spec Type
  | Syn_scope ([Syntree_node], Syntree_node)
  | Syn_tydef_decl String Type
  | Syn_fun_decl String [Syntree_node] Syntree_node Type
  | Syn_arg_def String Type
  | Syn_rec_decl String Type
  | Syn_var_decl String Type    
  | Syn_cond_expr (Syntree_node, (Syntree_node, Maybe Syntree_node)) Type
  | Syn_val Val Type
  | Syn_var String Type
  | Syn_expr_par Syntree_node Type
  | Syn_expr_call String [Syntree_node] Type
  | Syn_expr_una Operation Syntree_node Type
  | Syn_expr_bin Operation (Syntree_node, Syntree_node) Type
  | Syn_expr_seq [Syntree_node]
  | Syn_none
  deriving (Eq, Ord, Show)

expr_ty :: Syntree_node -> Type
expr_ty expr =
  case expr of
    Syn_ty_spec ty -> ty
    Syn_fun_decl _ _ _ ty -> ty
    Syn_arg_def _ ty -> ty
    Syn_var_decl _ ty -> ty
    Syn_cond_expr _ ty -> ty
    Syn_val _ ty -> ty
    Syn_var _  ty -> ty
    Syn_expr_par _ ty -> ty
    Syn_expr_call _ _ ty -> ty
    Syn_expr_una _ _ ty -> ty
    Syn_expr_bin _ _ ty -> ty
    _ -> Ty_unknown


data Error_codes =
  Internal_error String
  | Imcomplete_function_declaration
  | Imcomplete_type_specifier
  | Illegal_left_expression_for_assignment
  | Illegal_type_specified Tk_code
  | Illegal_operands Operation Syntree_node
  | Symbol_redifinition
  | Illegal_symbol_declaration
  | Unknown_token_detected
  deriving (Eq, Ord, Show)


par_type_decl :: [Tk_code] -> (Either [Error_codes] Type, [Tk_code])
par_type_decl tokens =
  case tokens of
    Tk_typed_as:[] -> (Left [Imcomplete_type_specifier], [])
    Tk_typed_as:ts -> (case ts of
                         Tk_bool:ts' -> (Right Ty_bool, ts')
                         Tk_int:ts' -> (Right Ty_int, ts')
                         t:ts' -> (Left [Illegal_type_specified t], ts')
                      )
    _ -> (Left [Internal_error "Calling cons_var_decl with non variable constructor."], tokens)

cons_var_decl :: Symtbl -> Syntree_node -> [Tk_code] -> ((Maybe Syntree_node, Symtbl, [Tk_code]), [Error_codes])
cons_var_decl symtbl var tokens =
  case var of
    Syn_var var_id var_ty -> (case tokens of
                                Tk_typed_as:ts -> (case par_type_decl tokens of
                                                     (Right var_ty', ts') -> let var_decl = Syn_var_decl var_id var_ty'
                                                                                 (symtbl', err_symreg) = sym_regist' (var_id, var_decl)
                                                                                 err = case err_symreg of
                                                                                   Just e_reg  -> [e_reg]
                                                                                   Nothing -> []
                                                                             in
                                                                               ((Just var_decl, symtbl', ts'), err)
                                                     (Left err, ts') -> let var_decl = Syn_var_decl var_id var_ty
                                                                            (symtbl', err_symreg) = sym_regist' (var_id, var_decl)
                                                                            err' = case err_symreg of
                                                                                     Just e_reg -> err ++ [e_reg]
                                                                                     Nothing -> err
                                                                        in
                                                                          ((Just var_decl, symtbl', ts'), err')
                                                  )
                                  where
                                    sym_regist' = sym_regist False symtbl Sym_cat_decl
                                
                                -- _ -> ((Syn_var var_id Ty_abs, tokens), [])
                                {- _ -> let var_decl = Syn_var_decl var_id var_ty
                                         (symtbl', err_symreg) = sym_regist False symtbl Sym_cat_decl (var_id, var_decl)
                                         err = case err_symreg of
                                           Just e_reg  -> [e_reg]
                                           Nothing -> []
                                     in
                                       ((Just var_decl, symtbl', tokens), err) -}
                                _ -> ((Nothing, symtbl, tokens), [])
                             )
    _ -> ((Just Syn_none, symtbl, tokens), [Internal_error "Calling cons_var_decl with non variable constructor."])


par_fun_decl :: Symtbl -> Syntree_node -> [Tk_code] -> ((Syntree_node, Symtbl, [Tk_code]), [Error_codes])
par_fun_decl symtbl fun tokens =
  let par_fun_type tokens =
        case tokens of
          Tk_typed_as:ts -> (case par_type_decl tokens  of
                               (Right ty, ts') -> ((ty, ts'), [])
                               (Left err, ts') -> ((Ty_abs, ts'), err)
                            )
          _ -> ((Ty_abs, tokens), [])
  in
    case fun of
      Syn_fun_decl fun_id args fun_body fun_ty -> (case tokens of
                                                     Tk_L_par:Tk_R_par:ts -> let ((fun_ty', tokens'), errs) = par_fun_type ts
                                                                                 fun_decl = Syn_fun_decl fun_id args fun_body fun_ty'
                                                                                 (symtbl', err_symreg) = sym_regist' (fun_id, fun_decl)
                                                                                 errs' = case err_symreg of
                                                                                           Just e_reg -> errs ++ [e_reg]
                                                                                           Nothing -> errs
                                                                             in
                                                                               ((fun_decl, symtbl', tokens'), errs')
                                                     Tk_L_par:ts -> let ((args', ts'), symtbl', arg_errs) = cons_args_decl symtbl ts
                                                                    in
                                                                      case ts' of
                                                                        Tk_R_par:ts'' -> let fun_decl = Syn_fun_decl fun_id (args ++ args') fun_body fun_ty'
                                                                                             (symtbl'', err_symreg) = sym_regist'' (fun_id, fun_decl)
                                                                                             errs' = case err_symreg of
                                                                                                       Just e_reg -> errs ++ [e_reg]
                                                                                                       Nothing -> errs
                                                                                         in
                                                                                           ((fun_decl, symtbl'', tokens'), errs')
                                                                          where
                                                                            ((fun_ty', tokens'), fun_ty_errs) = par_fun_type ts''
                                                                            sym_regist'' = sym_regist False symtbl' Sym_cat_decl
                                                                            errs = arg_errs ++ fun_ty_errs
                                                                        
                                                                        _ -> let fun_decl = Syn_fun_decl fun_id (args ++ args') fun_body fun_ty'
                                                                                 (symtbl'', err_symreg) = sym_regist'' (fun_id, fun_decl)
                                                                                 errs' = case err_symreg of
                                                                                           Just e_reg -> errs ++ [e_reg]
                                                                                           Nothing -> errs
                                                                             in
                                                                               ((fun_decl, symtbl'', tokens'), errs')
                                                                          where
                                                                            ((fun_ty', tokens'), fun_ty_errs) = par_fun_type ts'
                                                                            sym_regist'' = sym_regist False symtbl' Sym_cat_decl
                                                                            errs = arg_errs ++ [Imcomplete_function_declaration] ++ fun_ty_errs
                                                       where
                                                         cons_args_decl :: Symtbl -> [Tk_code] -> (([Syntree_node], [Tk_code]), Symtbl, [Error_codes])
                                                         cons_args_decl symtbl tokens =
                                                           case par_arg symtbl tokens of
                                                             (Nothing, symtbl', errs) -> (([], tokens), symtbl', errs)
                                                             (Just (arg, tokens'), symtbl', errs) -> (case tokens' of
                                                                                                        Tk_smcl:ts' -> ((arg:args, tokens''), symtbl'', errs ++ errs')
                                                                                                          where
                                                                                                            ((args, tokens''), symtbl'', errs') = cons_args_decl symtbl' ts'
                                                                                                        _ -> (([arg], tokens'), symtbl', errs)
                                                                                                     )
                                                         par_arg :: Symtbl -> [Tk_code] -> (Maybe (Syntree_node, [Tk_code]), Symtbl, [Error_codes])
                                                         par_arg symtbl tokens =
                                                           case tokens of
                                                             (Tk_ident arg_id):ts ->
                                                               let arg = Syn_var arg_id Ty_abs
                                                               in
                                                                 case cons_var_decl symtbl arg ts of
                                                                   ((Nothing, symtbl', ts'), errs) -> (Just (Syn_arg_def arg_id Ty_abs, ts'), symtbl', errs)
                                                                   ((Just (Syn_var_decl arg_id arg_ty), symtbl', ts'), errs) -> (Just (Syn_arg_def arg_id arg_ty, ts'), symtbl', errs)
                                                                   ((_, symtbl', ts'), errs) -> (Just (Syn_none, ts'), symtbl', errs)
                                                             _ -> (Nothing, symtbl, [])
                                                         
                                                         
                                                     _ -> let fun_decl = Syn_fun_decl fun_id args fun_body fun_ty'
                                                              (symtbl', err_symreg) = sym_regist' (fun_id, fun_decl)
                                                              errs' = case err_symreg of
                                                                        Just e_reg -> errs ++ [e_reg]
                                                                        Nothing -> errs
                                                          in
                                                            ((fun_decl, symtbl', tokens'), errs')
                                                       where
                                                         ((fun_ty', tokens'), fun_ty_errs) = par_fun_type tokens
                                                         errs =  [Imcomplete_function_declaration] ++ fun_ty_errs
                                                  )
        where
          sym_regist' = sym_regist False symtbl Sym_cat_decl
      
      _ -> ((Syn_none, symtbl, tokens), [Internal_error "Calling cons_var_decl with non variable constructor."])


cons_par_tree :: Symtbl -> [Tk_code] -> (Bool, Bool, Bool) -> (Maybe Syntree_node, Symtbl, [Tk_code])
cons_par_tree symtbl tokens (fun_declp, var_declp, par_contp) =
  let is_op t = (t == Tk_decre) || (t == Tk_incre) || (t == Tk_slash) || (t == Tk_star) || (t == Tk_shaft) || (t == Tk_cross) || (t == Tk_asgn)
      is_bin_op op = (op == Ope_add) || (op == Ope_sub) || (op == Ope_mul) || (op == Ope_div)
      is_gte_op ope1 ope2 = case ope1 of
                          Ope_add -> (case ope2 of
                                        Ope_add -> True
                                        Ope_sub -> True
                                        _ -> False
                                     )
                          Ope_sub -> (case ope2 of
                                        Ope_add -> True
                                        Ope_sub -> True
                                        _ -> False
                                     )
                          Ope_mul -> (case ope2 of
                                        Ope_add -> True
                                        Ope_sub -> True
                                        Ope_mul -> True
                                        Ope_div -> True
                                        -- _ -> False
                                     )
                          Ope_div -> (case ope2 of
                                        Ope_add -> True
                                        Ope_sub -> True
                                        Ope_mul -> True
                                        Ope_div -> True
                                        -- _ -> False
                                     )
      cons_expr symtbl subexpr1 tokens =
        let (ope, tokens') = fetch_ope tokens
        in
          case ope of
            Nothing -> (Right subexpr1, symtbl, tokens)
            Just ope' | ope' == Ope_asgn -> let left = cons_par_tree symtbl tokens' (False, False, True)
                                            in
                                              case left of
                                                (Just left_expr, symtbl', tokens'') -> (Right (Syn_expr_bin Ope_asgn (subexpr1, left_expr) Ty_abs), symtbl', tokens'')
                                                (Nothing, symtbl', tokens'') -> (Left Illegal_left_expression_for_assignment, symtbl', tokens'')
            Just ope' | is_bin_op ope' -> let r2 = cons_par_tree symtbl tokens' (False, False, True)
                                          in
                                            case r2 of
                                              (Just subexpr2, symtbl', tokens'') -> (case subexpr2 of
                                                                                       Syn_val _ _ -> (Right (Syn_expr_bin ope' (subexpr1, subexpr2) Ty_abs), symtbl', tokens'')
                                                                                       Syn_var _ _ -> (Right (Syn_expr_bin ope' (subexpr1, subexpr2) Ty_abs), symtbl', tokens'')
                                                                                       Syn_expr_bin bin_ope (expr_1, expr_2) _ ->
                                                                                         if is_gte_op ope' bin_ope then
                                                                                           (Right (Syn_expr_bin bin_ope ((leftmost_innermst subexpr1 ope' expr_1), expr_2) Ty_abs), symtbl', tokens'')
                                                                                         else
                                                                                           (Right (Syn_expr_bin ope' (subexpr1, subexpr2) Ty_abs), symtbl', tokens'')
                                                                                       _ -> (Right (Syn_expr_bin ope' (subexpr1, subexpr2) Ty_abs), symtbl', tokens'')
                                                                                    )
                                              (Nothing, symtbl', tokens'') -> (Left (Illegal_operands ope' Syn_none), symtbl', tokens'')
            _ -> (Left (Internal_error "Invalid operator detecded, in cons_expr."), symtbl, tokens)
        
        where
          fetch_ope tokens = case tokens of
                               (Tk_asgn:ts) -> (Just Ope_asgn, ts)
                               (Tk_slash:ts) -> (Just Ope_div, ts)
                               (Tk_star:ts) -> (Just Ope_mul, ts)
                               (Tk_shaft:ts) -> (Just Ope_sub, ts)
                               (Tk_cross:ts) -> (Just Ope_add, ts)
                               _ -> (Nothing, tokens)
          leftmost_innermst expr_li bin_ope expr0 =
            case expr0 of
              Syn_expr_bin ope_o (expr_o1@(Syn_val _ _), expr_o2) _ | is_gte_op bin_ope ope_o -> Syn_expr_bin ope_o ((Syn_expr_bin bin_ope (expr_li, expr_o1) Ty_abs), expr_o2) Ty_abs
              Syn_expr_bin ope_o (expr_o1@(Syn_var _ _), expr_o2) _ | is_gte_op bin_ope  ope_o -> Syn_expr_bin ope_o ((Syn_expr_bin bin_ope (expr_li, expr_o1) Ty_abs), expr_o2) Ty_abs
              Syn_expr_bin ope_o (expr_o1@(Syn_expr_bin ope_o1 _ _), expr_o2) _ | is_gte_op bin_ope ope_o -> Syn_expr_bin ope_o (leftmost_innermst expr_li bin_ope expr_o1, expr_o2) Ty_abs
              _ -> Syn_expr_bin bin_ope (expr_li, expr0) Ty_abs
      
      par_fun_call symtbl fun_app tokens =
        case fun_app of
          Syn_expr_call fun_id app_args app_ty -> (case tokens of
                                                     [] -> (Right fun_app, symtbl, tokens)
                                                     t:ts | is_op t -> (Right fun_app, symtbl, tokens)
                                                     _ -> (case cons_par_tree symtbl tokens (False, False, False) of
                                                             (Just arg, symtbl', tokens') -> par_fun_call symtbl' (Syn_expr_call fun_id (app_args ++ [arg]) app_ty) tokens'
                                                             (Nothing, symtbl', tokens') -> (Right fun_app, symtbl', tokens')
                                                          )
                                                  )
          _ -> (Left (Internal_error "Calling cons_var_decl with non variable constructor."), symtbl, tokens)
  in
    let cont_par symtbl subexpr tokens =
          if par_contp then (case cons_expr symtbl subexpr tokens of
                               (Right expr', symtbl', tokens') -> (Just expr', symtbl', tokens')
                               (Left err, symtbl', tokens') -> (Nothing, symtbl', tokens')
                            )
          else
            (Just subexpr, symtbl, tokens)
    in     
      case tokens of
        [] -> (Nothing, symtbl, [])
        Tk_L_par:ts -> (case cons_par_tree symtbl ts (False, False, True) of
                          (Just expr, symtbl', (Tk_R_par:ts')) -> cont_par symtbl' (Syn_expr_par expr (expr_ty expr)) ts'
                          (_, symtbl',ts') -> (Nothing, symtbl', ts')
                       )
        Tk_if:ts ->
          (case cons_par_tree symtbl ts (False, False, True) of
             (Just cond_expr, symtbl', (Tk_then:ts')) ->
               (case cons_par_tree symtbl' ts' (False, False, True) of               
                  (Just true_expr, symtbl'_t, (t'':ts'')) | t'' == Tk_else -> (case cons_par_tree symtbl'_t ts'' (False, False, True) of
                                                                                 (Just false_expr, symtbl'', tokens') ->
                                                                                   (Just (Syn_cond_expr (cond_expr, (true_expr, Just false_expr)) Ty_abs), symtbl'', tokens')
                                                                                 (_, symtbl'', tokens') -> (Nothing, symtbl'', tokens')
                                                                              )
                  (Just true_expr, symtbl'', tokens') -> (Just (Syn_cond_expr (cond_expr, (true_expr, Nothing)) Ty_abs), symtbl'', tokens')
                  (_, symtbl'', tokens') -> (Nothing, symtbl'', tokens')
               )
             (_, symtbl', tokens') -> (Nothing, symtbl', tokens')
          )                                        
        Tk_decre:ts -> (case ts of
                          (Tk_ident ident):ts' -> cont_par symtbl (Syn_expr_una Ope_decre (Syn_var ident Ty_abs) Ty_abs) ts'
                          _ -> (Nothing, symtbl, ts)
                       )
        Tk_incre:ts -> (case ts of
                          (Tk_ident ident):ts' -> cont_par symtbl (Syn_expr_una Ope_incre (Syn_var ident Ty_abs) Ty_abs) ts'
                          _ -> (Nothing, symtbl, ts)
                       )
        Tk_shaft:ts -> (case ts of
                          (Tk_ident ident):ts' -> cont_par symtbl (Syn_expr_una Ope_neg (Syn_var ident Ty_abs) Ty_abs) ts'
                          _ -> (Nothing, symtbl, ts)
                       )
        Tk_false:ts -> cont_par symtbl (Syn_val (Val_bool False) Ty_bool) ts
        Tk_true:ts -> cont_par symtbl (Syn_val (Val_bool True) Ty_bool) ts
        (Tk_nume n):ts -> cont_par symtbl (Syn_val (Val_int n) Ty_int) ts
        (Tk_str s):ts -> cont_par symtbl (Syn_val (Val_str s) Ty_string) ts
        Tk_fun:ts -> if fun_declp then
          case ts of
            (Tk_ident fun_id):ts' -> 
              let fun = Syn_fun_decl fun_id [] (Syn_scope ([], Syn_none)) Ty_abs
              in
                case par_fun_decl symtbl fun ts' of
                  ((fun@(Syn_fun_decl fun_id fun_args fun_body fun_ty), symtbl', (Tk_L_bra:ts'')), errs) -> do
                    let (symtbl'', err_funreg) = sym_regist False symtbl' Sym_cat_decl (fun_id, fun)
                    let (new_scope, errs_argreg) = Prelude.foldl (\(symtbl, errs) -> \arg@(Syn_arg_def arg_id _) -> case sym_regist False symtbl Sym_cat_decl (arg_id, arg) of
                                                                                                                      (symtbl', Just e_reg) -> (symtbl', errs ++ [e_reg])
                                                                                                                      (symtbl', Nothing) -> (symtbl', errs)
                                                                 ) ((sym_enter_scope (Just symtbl'') Sym_cat_decl), []) fun_args
                    let errs' = errs ++ (case err_funreg of
                                           Nothing -> []
                                           Just e_reg -> [e_reg]
                                        ) ++ errs_argreg
                    case fun_body of
                      (Syn_scope ([], Syn_none)) -> let ((var_decls, expr_par_trees), new_scope', us, errs_body) = parse_fun_body new_scope ts''
                                                        fun_body' = (var_decls, (case expr_par_trees of
                                                                                    [] -> Syn_none
                                                                                    [expr] -> expr
                                                                                    exprs -> Syn_expr_seq exprs
                                                                                 )                                                                      
                                                                    )
                                                        (fun', tokens') = (Syn_fun_decl fun_id fun_args (Syn_scope fun_body') fun_ty, us)
                                                        errs'' = errs' ++ errs_body
                                                    in
                                                      case tokens' of
                                                        Tk_R_bra:tokens'' -> (Just fun', new_scope', tokens'')
                                                        _ -> (Nothing, new_scope', tokens')
                        where
                          parse_fun_body :: Symtbl -> [Tk_code] -> (([Syntree_node], [Syntree_node]), Symtbl, [Tk_code], [Error_codes])
                          parse_fun_body symtbl tokens =
                            case cons_par_tree symtbl tokens (False, True, True) of
                              (Just var_decl@(Syn_var_decl _ _), symtbl', (Tk_smcl:tokens')) ->
                                let ((var_decls, expr_trees), symtbl'', tokens'', errs) = parse_fun_body symtbl' tokens'
                                in
                                  ((var_decl:var_decls, expr_trees), symtbl'', tokens'', errs)
                              (Just var_decl@(Syn_var_decl _ _), symtbl', tokens') ->
                                let ((var_decls, expr_trees), symtbl'', tokens'', errs) = parse_fun_body symtbl' tokens'
                                in
                                  case var_decls of
                                    [] -> (([var_decl], expr_trees), symtbl'', tokens'', errs)
                                    _ -> (([var_decl], expr_trees), symtbl'', tokens'', [Illegal_symbol_declaration] ++ errs)
                              (Just expr_par_tree, symtbl', Tk_smcl:tokens') ->
                                let ((var_decls, expr_trees), symtbl'', tokens'', errs) = parse_fun_body symtbl' tokens'
                                in
                                  case var_decls of
                                    [] -> (([], expr_par_tree:expr_trees), symtbl'', tokens'', errs)
                                    _ -> (([], expr_par_tree:expr_trees), symtbl'', tokens'', errs ++ [Illegal_symbol_declaration])
                              (Just expr_par_tree, symtbl', tokens') ->
                                let ((var_decls, expr_trees), symtbl'', tokens'', errs) = parse_fun_body symtbl' tokens'
                                in
                                  case (var_decls, expr_trees) of
                                    ([], []) -> (([], [expr_par_tree]), symtbl'', tokens'', errs)
                                    _ -> (([], [expr_par_tree]), symtbl'', tokens'', errs ++ [Illegal_symbol_declaration])
                              (Nothing, symtbl', tokens') -> (([], []), symtbl', tokens', [])
                      
                      _ -> (Nothing, new_scope, ts')
                  ((_, symtbl',tokens'), errs) -> (Nothing, symtbl', tokens')
            _:ts' -> (Nothing, symtbl, ts')
          else (Nothing, symtbl, ts)
        (Tk_ident ident):ts -> let var = Syn_var ident Ty_abs                                
                               in
                                 if var_declp then
                                   case cons_var_decl symtbl var ts of
                                     ((Just var_decl, symtbl', tokens'), errs) -> (Just var_decl, symtbl', tokens')
                                     ((Nothing, symtbl', tokens'@(t:ts')), errs) | not (is_op t) ->
                                                                                   let fun_app = Syn_expr_call ident [] Ty_abs 
                                                                                   in
                                                                                     case par_fun_call symtbl' fun_app tokens' of
                                                                                       (Right (fun_app'@(Syn_expr_call fun_id app_args app_ty)), symtbl'', tokens'') ->
                                                                                         cont_par symtbl'' fun_app' tokens''
                                                                                       (Left err, symtbl'', tokens'') -> (Nothing, symtbl'', tokens'')
                                     ((_, symtbl', tokens'), errs) -> cont_par symtbl' var tokens'
                                 else
                                   cont_par symtbl var ts
        _ -> (Nothing, symtbl, tokens)


type Fresh_tvar = (Type, Integer)

first_flesh_tvar :: Fresh_tvar
first_flesh_tvar = (Ty_var $ "t_" ++ (show 0), 0)

succ_flesh_tvar :: Fresh_tvar -> Fresh_tvar
succ_flesh_tvar prev =
  (Ty_var $ "t_" ++ show (last_id + 1), last_id + 1)
  where
    last_id = (snd prev)


curve_tvars :: (Syntree_node, Fresh_tvar) -> (Syntree_node, Fresh_tvar)
curve_tvars (expr, prev_tvar) =
  (case expr of
     Syn_arg_def arg_id Ty_abs -> let latest = succ_flesh_tvar prev_tvar
                                  in
                                    (Syn_arg_def arg_id (fst latest), latest)
     Syn_var var_id Ty_abs -> let latest = succ_flesh_tvar prev_tvar
                              in
                                (Syn_var var_id (fst latest), latest)
     Syn_expr_par expr' Ty_abs -> let (expr_abs, prev_tvar') = curve_tvars (expr', prev_tvar)
                                      latest = succ_flesh_tvar prev_tvar'
                                  in
                                    (Syn_expr_par expr_abs (fst latest), latest)
     Syn_expr_una ope_una expr' Ty_abs -> let (expr_abs, prev_tvar') = curve_tvars (expr', prev_tvar)
                                              latest = succ_flesh_tvar prev_tvar'
                                          in
                                            (Syn_expr_una ope_una expr_abs (fst latest), latest)
     Syn_expr_bin ope_bin (expr1, expr2) Ty_abs -> let (expr1_abs, prev_tvar') = curve_tvars (expr1, prev_tvar)
                                                       (expr2_abs, prev_tvar'') = curve_tvars (expr2, prev_tvar')
                                                       latest = succ_flesh_tvar prev_tvar''
                                                   in
                                                     (Syn_expr_bin ope_bin (expr1_abs, expr2_abs) (fst latest), latest)
     Syn_expr_call fun_id args Ty_abs -> (case args of
                                            [] -> let latest = succ_flesh_tvar prev_tvar
                                                  in
                                                    (Syn_expr_call fun_id [] (fst latest), latest)
                                            _ -> let (args_abs, prev_tvar') = abs_args args prev_tvar
                                                     latest = succ_flesh_tvar prev_tvar'
                                                 in
                                                   (Syn_expr_call fun_id args_abs (fst latest), latest)
                                              where
                                                abs_args = abs_decls
                                         )
     Syn_cond_expr (cond_expr, (true_expr, false_expr)) Ty_abs -> let (cond_expr', prev_tvar') = curve_tvars (cond_expr, prev_tvar)
                                                                      (true_expr', prev_tvar'') = curve_tvars (true_expr, prev_tvar')
                                                                  in
                                                                    case false_expr of
                                                                      Just f_expr_body -> let (f_expr_body', latest) = curve_tvars (f_expr_body, prev_tvar'')
                                                                                              latest' = succ_flesh_tvar latest
                                                                                          in
                                                                                            (Syn_cond_expr (cond_expr', (true_expr', Just f_expr_body')) (fst latest'), latest')
                                                                      Nothing -> let latest = succ_flesh_tvar prev_tvar''
                                                                                 in
                                                                                   (Syn_cond_expr (cond_expr', (true_expr', Nothing)) (fst latest), latest)
     Syn_fun_decl fun_id args fun_body fun_ty  -> (case args of
                                                     [] -> let (body_abs, prev_tvar') = curve_tvars (fun_body, prev_tvar)
                                                               latest = succ_flesh_tvar prev_tvar'
                                                           in
                                                             (Syn_fun_decl fun_id [] body_abs (fst latest), latest)
                                                     _ -> let (args_abs, prev_tvar') = abs_decls args prev_tvar
                                                              (body_abs, prev_tvar'') = curve_tvars (fun_body, prev_tvar')
                                                              (fun_ty', latest) = abs_funty (args_abs, fun_ty) prev_tvar''
                                                          in
                                                            (Syn_fun_decl fun_id args_abs body_abs fun_ty', latest)
                                                       where
                                                         abs_funty :: ([Syntree_node], Type) -> Fresh_tvar -> (Type, Fresh_tvar)
                                                         abs_funty (args, fun_ty) prev_tvar =
                                                           let from_args = Prelude.foldl (\(tys, prev_tv) -> (\a -> case expr_ty a of
                                                                                                                      Ty_abs -> let prev_tv' = succ_flesh_tvar prev_tv
                                                                                                                                in
                                                                                                                                  (tys ++ [(fst prev_tv')], prev_tv')
                                                                                                                      (a_ty@_) -> (tys ++ [a_ty], prev_tv)
                                                                                                             )
                                                                                         ) ([], prev_tvar) args
                                                           in
                                                             case from_args of
                                                               (ty_args, prev_tvar') -> (case fun_ty of
                                                                                           Ty_abs -> (Ty_fun (ty_args ++ [(fst latest)]), latest)
                                                                                             where
                                                                                               latest = succ_flesh_tvar prev_tvar'
                                                                                           _ -> (Ty_fun (ty_args ++ [fun_ty]), prev_tvar')
                                                                                        )
                                                  )
     Syn_var_decl var_id Ty_abs -> let latest = succ_flesh_tvar prev_tvar
                                   in
                                     (Syn_var_decl var_id (fst latest), latest)
     Syn_expr_seq exprs -> (case exprs of
                              [] -> (Syn_expr_seq [], prev_tvar)
                              e:es -> let (e', prev_tvar') = curve_tvars (e, prev_tvar)
                                          (es', latest) = abs_exprs es prev_tvar'
                                      in
                                        (Syn_expr_seq (e':es'), latest)
                                where
                                  abs_exprs = abs_decls
                           )
     Syn_scope (decls, body) -> let (decls', prev_tvar') = abs_decls decls prev_tvar
                                    (body', latest) = curve_tvars (body, prev_tvar')
                                in
                                  (Syn_scope (decls', body'), latest)
     _ -> (expr, prev_tvar)
  )
  where
    abs_decls :: [Syntree_node] -> Fresh_tvar -> ([Syntree_node], Fresh_tvar)
    abs_decls args prev_tvar =
      case args of
        [] -> ([], prev_tvar)
        a:as -> let (a', prev_tvar') = curve_tvars (a, prev_tvar)
                    (as', prev_tvar'') = abs_decls as prev_tvar'
                in
                  (a':as', prev_tvar'')


data Ty_env =
  Ty_env [(String, Type)]
  deriving (Eq, Show)

ty_inf :: Maybe [Syntree_node] -> Maybe (Ty_env, Syntree_node)
ty_inf expr =
  --{(var_id, var_ty)} |- var_id : var_ty, s.t. "var_ty var_id" in declration form
  case expr of
    Just ((c@(Syn_val (Val_bool b) ty_b)):es) -> if (ty_b == Ty_bool) then Just (Ty_env [], c) else Nothing
    Just ((c@(Syn_val (Val_int n) ty_n)):es) -> if (ty_n == Ty_int) then Just (Ty_env [], c) else Nothing
    Just ((c@(Syn_val (Val_str s) ty_s)):es) -> if (ty_s == Ty_string) then Just (Ty_env [], c) else Nothing
    Just ((v@(Syn_var var_id var_ty)):es) -> Just (Ty_env [(var_id, var_ty)], v)
    Just ((Syn_expr_una ope exp _):es) -> do
      (env, typng) <- ty_inf (Just [exp])
      ty' <- (case typng of
                Syn_val _ ty -> Just ty
                Syn_var _ ty -> Just ty
                Syn_expr_una _ _ ty -> Just ty
                Syn_expr_bin _ _ ty -> Just ty
                _ -> Nothing
             )
      return (env, Syn_expr_una ope exp ty')
    Just ((Syn_expr_bin ope (exp_l, exp_r) _):es) -> do
      (Ty_env env_l, typng_l) <- ty_inf (Just [exp_l])
      (Ty_env env_r, typng_r) <- ty_inf (Just [exp_r])
      ty' <- (case typng_l of
                Syn_val _ ty_l -> (case typng_r of
                                     Syn_val _ ty_r -> gct ty_l ty_r
                                     Syn_var _ ty_r -> gct ty_l ty_r
                                     Syn_expr_una _ _ ty_r -> gct ty_l ty_r
                                     Syn_expr_bin _ _ ty_r -> gct ty_l ty_r
                                     _ -> Nothing
                                  )
                Syn_var var_id ty_l -> (case typng_r of
                                          Syn_val _ ty_r -> gct ty_l ty_r
                                          Syn_var _ ty_r -> gct ty_l ty_r
                                          Syn_expr_una _ _ ty_r -> gct ty_l ty_r
                                          Syn_expr_bin _ _ ty_r -> gct ty_l ty_r
                                          _ -> Nothing
                                       )
                Syn_expr_una _ _ ty_l -> (case typng_r of
                                            Syn_val _ ty_r -> gct ty_l ty_r
                                            Syn_var _ ty_r -> gct ty_l ty_r
                                            Syn_expr_una _ _ ty_r -> gct ty_l ty_r
                                            Syn_expr_bin _ _ ty_r -> gct ty_l ty_r
                                            _ -> Nothing
                                         )
                Syn_expr_bin _ _ ty_l -> (case typng_r of
                                            Syn_val _ ty_r -> gct ty_l ty_r
                                            Syn_var _ ty_r -> gct ty_l ty_r
                                            Syn_expr_una _ _ ty_r -> gct ty_l ty_r
                                            Syn_expr_bin _ _ ty_r -> gct ty_l ty_r
                                            _ -> Nothing
                                         )
                _ -> Nothing
             )
      exp_l' <- return (case typng_l of
                          Syn_var var_id _ ->  Syn_var var_id ty'
                          _ -> exp_l
                       )
      exp_r' <- return (case typng_r of
                          Syn_var var_id _ ->  Syn_var var_id ty'
                          _ -> exp_r
                       )
      
      env_l' <- return (case typng_l of
                          Syn_var var_id _ -> M.toList $ M.insert var_id ty' $ M.delete var_id (M.fromList env_l)
                          _ -> env_l
                       )
      env_r' <- return (case typng_r of
                          Syn_var var_id _ -> M.toList $ M.insert var_id ty' $ M.delete var_id (M.fromList env_r)
                          _ -> env_r
                       )
      env' <- merge_env (Ty_env env_l') (Ty_env env_r')
      return (env', Syn_expr_bin ope (exp_l', exp_r') ty')
    _ -> Nothing
  
  where
    gct :: Type -> Type -> Maybe Type
    gct ty_1 ty_2 =  
      let is_subty ty_1 ty_2 =
            case ty_2 of
              Ty_top -> True
              Ty_bool -> (case ty_1 of
                            Ty_btm -> True
                            Ty_abs -> True
                            Ty_bool -> True
                            _ -> False
                         )
              Ty_string -> (case ty_1 of
                              Ty_btm -> True
                              Ty_abs -> True
                              Ty_string -> True
                              _ -> False
                           )
              Ty_int -> (case ty_1 of
                           Ty_btm -> True
                           Ty_abs -> True
                           Ty_int -> True
                           _ -> False
                        )
              Ty_pair (ty_21, ty_22) -> (case ty_1 of
                                           Ty_pair (ty_11, ty_12) -> (is_subty ty_11 ty_21) && (is_subty ty_12 ty_22)
                                           _ -> False
                                        )
              Ty_abs -> (case ty_1 of
                           Ty_btm -> True
                           Ty_abs -> True
                           _ -> False
                        )
              _ -> False
      in
        if (is_subty ty_1 ty_2) then Just ty_2
        else
          if (is_subty ty_2 ty_1) then Just ty_1 else Nothing
    
    merge_env :: Ty_env -> Ty_env -> Maybe Ty_env
    merge_env env_1 env_2 =
      case env_2 of
        Ty_env [] -> Just env_1
        Ty_env env2_body -> (case env_1 of
                               Ty_env [] -> Just env_2
                               Ty_env env1_body -> (case chk_and_merge env1_body env2_body of
                                                      Just merged_body -> Just (Ty_env merged_body)
                                                      Nothing -> Nothing
                                                   )
                            )
        where
          chk_and_merge env1_body env2_body =
            Prelude.foldl (\e1 -> \(id, ty) -> do
                        e1' <- e1
                        e1'' <- (case Prelude.lookup id e1' of
                                   Just _ -> Nothing
                                   Nothing -> Just e1'
                                )
                        return ((id, ty) : e1'')
                    ) (Just env1_body) env2_body


main :: IO ()
main = do
  -- src = "bool fun x => (2)"
  -- src = "int boola fun x => (2)"
  -- src = "(alpha - beta) + gamma"
  -- src = "b+a + 2"
  -- src = "fun a () { b }"
  -- src = "fun a (g as int) { b + a + 3 * 5; c + d }"
  -- src = "fun a (g as int) { c + (b + a) }"
  -- src = "fun a (g as int) { -c - ++d + (b - -a) }"
  -- src = "fun a (g as int) { h as int; i as int; x + w; }"
  h <- openFile "src.txt" ReadMode
  src <- read_src h
  
  let tokens = conv2_tokens src
  putStrLn $ "source:  " ++ (show src)
  putStrLn $ "tokens:  " ++ (show tokens)
  symtbl <- return $ sym_enter_scope Nothing Sym_cat_decl
  (syn_forest, symtbl')  <- return $ case (snd tokens) of
                                       "" -> let (syn_tree, symtbl', tokens') = cons_par_tree symtbl (fst tokens) (True, True, True)
                                             in
                                               case syn_tree of
                                                 Just s_tree -> let (s_trees, symtbl'') = cons_par_trees symtbl' tokens'
                                                                in
                                                                  (Just (s_tree:s_trees), symtbl'')
                                                 _ -> (Nothing, symtbl')
                                         where
                                           cons_par_trees symtbl [] = ([], symtbl)
                                           cons_par_trees symtbl (t:ts) =
                                             let (syn_tree, symtbl', ts') = cons_par_tree symtbl ts (True, True, True)
                                             in
                                               case syn_tree of
                                                 Just s_tree -> let (s_trees, symtbl'') = cons_par_trees symtbl' ts'
                                                                in
                                                                  (s_tree:s_trees, symtbl'')
                                                 _ -> ([], symtbl')
                                       _ -> (Nothing, symtbl)
  putStrLn $ "p-trees: " ++ (show syn_forest)
  
  putStr "ty-abs:  "
  ty_abs <- return $ case syn_forest of
                       Just syns -> let (forest_abs, _) = Prelude.foldl (\(stmts, prev_tv) -> (\stmt -> let (stmt_abs, prev_tv') = curve_tvars (stmt, prev_tv)
                                                                                                        in
                                                                                                          (stmts ++ [stmt_abs], prev_tv')
                                                                                              )
                                                                        ) ([], first_flesh_tvar) syns
                                    in
                                      forest_abs
                       _ -> []
  mapM_ putStrLn $ Prelude.map show ty_abs
  
  putStrLn $ "ty-inf:  " ++ (maybe "" show (ty_inf syn_forest))
    
    where
      read_src :: Handle -> IO String
      read_src h = do
        eof <- hIsEOF h
        if eof then return []
          else do
          str <- hGetLine h
          str' <- read_src h
          return $ str ++ str'
