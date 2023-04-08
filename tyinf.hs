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

import Data.Either (isLeft, isRight)
import Data.Map as M
import Data.Set as Set
import Control.Monad.State as St
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Control.Exception as Except
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
sym_crnt_level :: Sym_tbl -> Scope_Lvl
sym_crnt_level Scope_empty = 0
sym_crnt_level (Scope_add ( lv, _, _ ) _) = lv

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
                                     Scope_empty -> Scope_add (1, Symtbl_anon_ident {sym_anon_var = 1, sym_anon_record = 1}, Sym_empty) Scope_empty
                                     Scope_add (lv, sym_anon_ident, _) _ -> Scope_add (lv + 1, sym_anon_ident, Sym_empty) sym_tbl
                    in
                      sym_update s_tbl cat sym_tbl'
    Nothing -> let symtbl0 = Symtbl {sym_typedef = Scope_empty, sym_record = Scope_empty, sym_func = Scope_empty, sym_decl = Scope_empty}
               in
                 sym_enter_scope (Just symtbl0) cat
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
                                                                                  Just e -> if (not ovwt) then (sym_tbl, Just Symbol_redefinition)
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
                                                                                  Just e -> if (not ovwt) then (sym_tbl, Just (Symbol_redefinition errmsg))
                                                                                            else ((Scope_add (lv, anon_idents, (Sym_add sym syms)) sym_tbls), Nothing)
                                                                                    where
                                                                                      errmsg = "symbol table error, failed to register, " ++
                                                                                               "for detection of pre registered object with same identifier as " ++ ident
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
  deriving (Eq, Show)


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
  | Tk_comma
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
  | Par_keyword_var_1
  | Par_keyword_var_2
  | Par_acc Tk_code
  | Par_err
  deriving (Eq, Ord, Show)


is_blank c = ((c == ' ') || (c == '\t'))

is_delim c =
  case c of
    ' ' -> True
    '\t' -> True
    '=' -> True
    ',' -> True
    '>' -> True
    '{' -> True
    '(' -> True
    '<' -> True
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
            Par_ini | (c == 'v') -> ((Par_keyword_var_1, quo_stat), cs)
            
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

            Par_keyword_var_1 | (c == 'a') -> ((Par_keyword_var_2, quo_stat), cs)
            Par_keyword_var_1 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("v" ++ [c]))), cs)
                                 else ((Par_acc (Tk_ident "v"), Nothing), src)
            Par_keyword_var_2 | (c == 'r') -> (case cs of
                                                 [] -> ((Par_acc Tk_var, quo_stat), "")
                                                 c':cs' | (is_delim c') -> ((Par_acc Tk_var, quo_stat), cs)
                                                 _ -> ((Par_str, Just (No_quoted "var")), cs)
                                              )   
            Par_keyword_var_2 -> if (is_alnum c) then ((Par_str, Just (No_quoted ("va" ++ [c]))), cs)
                                 else ((Par_acc (Tk_ident "va"), Nothing), src)
            
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
                ',' -> (Par_acc Tk_comma, crnt_quo_stat)
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
  | Ty_fun [Type] Type
  | Ty_abs
  | Ty_btm
  | Ty_prom Type Type
  | Ty_ovride Type Type
  | Ty_unknown
  deriving (Eq, Ord, Show)

type Ty_env_bind = [(String, Type)]
data Ty_env =
  --Ty_env [(String, Type)]
  Ty_env Ty_env_bind
  deriving (Eq, Ord, Show)

type Subst = (String, Type)

ty_subst :: [Subst] -> Type -> Type
ty_subst subst ty_expr =
  case subst of
    [] -> ty_expr
    s:ss -> ty_subst ss (subst1 s ty_expr)
      where
        subst1 :: Subst -> Type -> Type
        subst1 (subst@(tvar_id, ty_mapsto)) ty_expr =
          case ty_expr of
            Ty_top -> ty_expr
            Ty_bool -> ty_expr
            Ty_string -> ty_expr
            Ty_int -> ty_expr              
            Ty_var id -> if id == tvar_id then ty_mapsto else ty_expr
            Ty_pair (ty_expr1, ty_expr2) -> Ty_pair (subst1 subst ty_expr1, subst1 subst ty_expr2)
            Ty_fun ty_args ty_expr -> Ty_fun (Prelude.map (subst1 subst) ty_args) (subst1 subst ty_expr)
            Ty_abs -> ty_expr
            Ty_btm -> ty_expr
            Ty_prom ty_prev ty_crnt -> Ty_prom ty_prev (subst1 subst ty_crnt)
            Ty_ovride ty_prev ty_crnt -> Ty_ovride ty_prev (subst1 subst ty_crnt)
            Ty_unknown -> ty_expr

ty_subst_env :: [Subst] -> Ty_env -> Ty_env
ty_subst_env subst env =
  case env of
    Ty_env [] -> env
    Ty_env ((v_id, v_ty):es) -> let v_ty' = ty_subst subst v_ty
                                in
                                  Ty_env $ (v_id, v_ty'):(case ty_subst_env subst (Ty_env es) of
                                                            Ty_env es' -> es'
                                                         )

ty_ftv :: Type -> [String]
ty_ftv ty_expr =
  case ty_expr of
    Ty_ovride _ t_exp' -> ty_ftv t_exp'
    Ty_prom _ t_exp' -> ty_ftv t_exp'
    Ty_var tvar_id -> [tvar_id]
    Ty_pair (t_exp1, t_exp2) -> (ty_ftv t_exp1) ++ (ty_ftv t_exp2)
    Ty_fun args t_exp ->  Set.toList $ Set.union (Set.fromList (case args of
                                                                 [] -> []
                                                                 _ -> Prelude.foldr (\a -> \ftvs -> let tvs_a = ty_ftv a
                                                                                                    in
                                                                                                      Set.toList $ Set.union (Set.fromList tvs_a) (Set.fromList ftvs)
                                                                                    ) [] args
                                                               )
                                                 ) (Set.fromList $ ty_ftv t_exp)
    _ -> [] -- for Ty_top, Ty_bool, Ty_string, Ty_int, Ty_abs, Ty_btm and Ty_unknown


-- returns Least Common Supertype, as ty_1 <: ty_2, if exists.
ty_lcs :: Type -> Type -> Maybe Type
ty_lcs ty_1 ty_2 =
  let is_subty ty_1 ty_2 =
        case ty_2 of
          Ty_top -> True
          Ty_ovride _ ty_2' -> is_subty ty_1 ty_2'
          Ty_prom _ ty_2' -> is_subty ty_1 ty_2'
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
          _ -> False
  in
    if (is_subty ty_1 ty_2) then Just ty_2
    else
      if (is_subty ty_2 ty_1) then Just ty_1 else Nothing


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
  Syn_scope ([Syntree_node], Syntree_node)
  | Syn_tydef_decl String Type
  | Syn_fun_decl' String [Syntree_node] Syntree_node (Ty_env, Type)
  | Syn_fun_decl String [Syntree_node] Syntree_node Type
  | Syn_arg_decl String Type
  | Syn_rec_decl String Type
  | Syn_var_decl String Type
  | Syn_cond_expr (Syntree_node, (Syntree_node, Maybe Syntree_node)) Type
  | Syn_val Val Type
  | Syn_var String Type
  | Syn_expr_asgn Syntree_node Syntree_node Type
  | Syn_expr_par Syntree_node Type
  | Syn_expr_call String [Syntree_node] Type
  | Syn_expr_una Operation Syntree_node Type
  | Syn_expr_bin Operation (Syntree_node, Syntree_node) Type
  | Syn_expr_seq [Syntree_node] Type
  | Syn_none
  deriving (Eq, Ord, Show)

syn_node_typeof :: Syntree_node -> Type
syn_node_typeof expr =
  case expr of
    Syn_tydef_decl _ ty -> ty
    Syn_fun_decl' _ _ _ (_, ty) -> ty
    Syn_fun_decl _ _ _ ty -> ty
    Syn_arg_decl _ ty -> ty
    Syn_rec_decl _  ty -> ty
    Syn_var_decl _ ty -> ty
    Syn_cond_expr _ ty -> ty
    Syn_val _ ty -> ty
    Syn_var _  ty -> ty
    Syn_expr_asgn _ _ ty -> ty
    Syn_expr_par _ ty -> ty
    Syn_expr_call _ _ ty -> ty
    Syn_expr_una _ _ ty -> ty
    Syn_expr_bin _ _ ty -> ty
    Syn_scope (_, scp_body) -> syn_node_typeof scp_body
    Syn_expr_seq _ ty -> ty
    _ -> Ty_unknown -- Syn_none

syn_retrieve_typeof :: Syntree_node -> Type
syn_retrieve_typeof expr =
  case expr of
    Syn_expr_seq e_seq ty_seq -> case e_seq of
                                   [] -> Ty_btm
                                   [e] -> syn_retrieve_typeof e
                                   e:es -> syn_retrieve_typeof (Syn_expr_seq es ty_seq)
    _ -> syn_node_typeof expr

syn_node_promote :: Syntree_node -> Type -> Syntree_node
syn_node_promote expr ty_prom =
  if (syn_node_typeof expr) /= ty_prom then
    case expr of
      Syn_scope _ -> expr
      Syn_tydef_decl id ty -> Syn_tydef_decl id (Ty_prom ty ty_prom)
      Syn_fun_decl' id args body (env, ty) -> Syn_fun_decl' id args body (env, (Ty_prom ty ty_prom))
      Syn_fun_decl id args body ty -> Syn_fun_decl id args body (Ty_prom ty ty_prom)
      Syn_arg_decl id ty -> Syn_arg_decl id (Ty_prom ty ty_prom)
      Syn_rec_decl id ty -> Syn_rec_decl id (Ty_prom ty ty_prom)
      Syn_var_decl id ty -> Syn_var_decl id (Ty_prom ty ty_prom)
      Syn_cond_expr body ty -> Syn_cond_expr body (Ty_prom ty ty_prom)
      Syn_val v ty -> Syn_val v (Ty_prom ty ty_prom)
      Syn_var id ty -> Syn_var id (Ty_prom ty ty_prom)
      Syn_expr_asgn expr_l expr_r ty -> Syn_expr_asgn expr_l expr_r (Ty_prom ty ty_prom)
      Syn_expr_par body ty -> Syn_expr_par body (Ty_prom ty ty_prom)
      Syn_expr_call id args ty -> Syn_expr_call id args (Ty_prom ty ty_prom)
      Syn_expr_una ope body ty -> Syn_expr_una ope body (Ty_prom ty ty_prom)
      Syn_expr_bin ope body ty -> Syn_expr_bin ope body (Ty_prom ty ty_prom)
      Syn_expr_seq body ty -> Syn_expr_seq body (Ty_prom ty ty_prom)
      _ -> expr -- Syn_none
  else expr

syn_node_subst :: [Subst] -> Syntree_node -> Syntree_node
syn_node_subst subst expr =
  case expr of   
    Syn_scope (decls, body) -> Syn_scope ((Prelude.map (syn_node_subst subst) decls), syn_node_subst subst body)
    Syn_tydef_decl ty_id ty -> Syn_tydef_decl ty_id (ty_subst subst ty)
    Syn_fun_decl' fun_id args body (env, ty) -> Syn_fun_decl' fun_id (Prelude.map (syn_node_subst subst) args) (syn_node_subst subst body) ((ty_subst_env subst env),(ty_subst subst ty))
    Syn_fun_decl fun_id args body ty -> Syn_fun_decl fun_id (Prelude.map (syn_node_subst subst) args) (syn_node_subst subst body) (ty_subst subst ty)
    Syn_arg_decl arg_id ty -> Syn_arg_decl arg_id (ty_subst subst ty)
    Syn_rec_decl rec_id ty -> Syn_rec_decl rec_id (ty_subst subst ty)
    Syn_var_decl var_id ty -> Syn_var_decl var_id (ty_subst subst ty)
    Syn_cond_expr (expr_cond, (expr_true, expr_false)) ty -> let expr_cond' = syn_node_subst subst expr_cond
                                                                 expr_true' = syn_node_subst subst expr_true
                                                                 expr_false' = case expr_false of
                                                                                 Nothing -> Nothing
                                                                                 Just f_expr -> Just (syn_node_subst subst f_expr)
                                                             in
                                                               Syn_cond_expr (expr_cond', (expr_true', expr_false')) (ty_subst subst ty)
    Syn_val val ty -> Syn_val val (ty_subst subst ty)
    Syn_var var_id ty -> Syn_var var_id (ty_subst subst ty)
    Syn_expr_asgn expr_l expr_r ty -> Syn_expr_asgn expr_l expr_r (ty_subst subst ty)
    Syn_expr_par expr_par ty -> Syn_expr_par (syn_node_subst subst expr_par) (ty_subst subst ty)   
    Syn_expr_call fun_id args ty -> Syn_expr_call fun_id (Prelude.map (syn_node_subst subst) args) (ty_subst subst ty)
    Syn_expr_una ope expr0 ty -> Syn_expr_una ope (syn_node_subst subst expr0) (ty_subst subst ty)
    Syn_expr_bin ope (expr1, expr2) ty -> Syn_expr_bin ope (syn_node_subst subst expr1, syn_node_subst subst expr2) (ty_subst subst ty)
    Syn_expr_seq equs ty -> Syn_expr_seq (Prelude.map (syn_node_subst subst) equs) (ty_subst subst ty)
    _ -> expr -- Syn_none


data Excep_codes =
  Excep_assert_failed
  | Excep_internal_error String
  deriving (Eq, Ord, Show)

data Error_Excep =
  Error_Excep Excep_codes String
  deriving (Eq, Ord, Show)


data Error_codes =
  Internal_error String
  | Parse_error String
  | Illtyped_constant
  | Ill_formed_expression String
  | Type_constraint_mismatched String
  | Imcomplete_function_declaration String
  | Imcomplete_variable_declaration String
  | Imcomplete_type_specifier
  | Illegal_left_expression_for_assignment
  | Illegal_type_specified Tk_code
  | Illegal_operands Operation Syntree_node
  | Undefined_symbol String
  | Symbol_redefinition String
  | Illegal_symbol_declaration
  | Unknown_token_detected
  deriving (Eq, Ord, Show)


{- par_type_decl :: [Tk_code] -> (Either [Error_codes] Type, [Tk_code])
par_type_decl tokens =
  case tokens of
    Tk_typed_as:[] -> (Left [Imcomplete_type_specifier], [])
    Tk_typed_as:ts -> (case ts of
                         Tk_bool:ts' -> (Right Ty_bool, ts')
                         Tk_int:ts' -> (Right Ty_int, ts')
                         t:ts' -> (Left [Illegal_type_specified t], ts)
                      )
    _ -> (Left [Internal_error "Calling cons_var_decl with non variable constructor."], tokens) -}
    
par_type_decl1 :: Symtbl -> [Tk_code] -> ExceptT Error_Excep IO (Either [Error_codes] Type, Symtbl, [Tk_code])
par_type_decl1 symtbl tokens =
  case tokens of
    Tk_typed_as:[] -> return (Left [Imcomplete_type_specifier], symtbl, [])
    Tk_typed_as:ts -> return (case ts of
                                Tk_bool:ts' -> (Right Ty_bool, symtbl, ts')
                                Tk_int:ts' -> (Right Ty_int, symtbl, ts')
                                t:ts' -> (Left [Illegal_type_specified t], symtbl, ts)
                             )
    _ -> let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
         in
           throwE (Error_Excep Excep_assert_failed loc)


{- cons_var_decl :: Symtbl -> Syntree_node -> [Tk_code] -> ((Maybe Syntree_node, Symtbl, [Tk_code]), [Error_codes])
cons_var_decl symtbl var tokens =
  case var of
    Syn_var var_id var_ty ->
      (case tokens of
         Tk_typed_as:ts -> (case par_type_decl tokens of
                              (Right var_ty', ts') -> ((Just (Syn_var_decl var_id var_ty'), symtbl, ts'), [])
                              (Left err, ts') -> ((Just (Syn_var_decl var_id var_ty), symtbl, ts'), err)
                           )
         _ -> ((Just (Syn_var_decl var_id var_ty), symtbl, tokens), [])
      )
    _ -> assert False (let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                       in
                          ((Just Syn_none, symtbl, tokens), [Internal_error errmsg])
                      ) -}

cons_var_decl1 :: Symtbl -> Syntree_node -> [Tk_code] -> ExceptT Error_Excep IO ((Maybe Syntree_node, Symtbl, [Tk_code]), [Error_codes])
cons_var_decl1 symtbl var tokens =
  case var of
    Syn_var var_id var_ty -> do
      r <- lift (case tokens of
                   Tk_typed_as:ts -> do
                     r_ty <- runExceptT $ par_type_decl1 symtbl tokens
                     return (case r_ty of
                               Left err -> Left err
                               Right (Right var_ty', symtbl', ts') -> Right ((Just (Syn_var_decl var_id var_ty'), symtbl', ts'), [])
                               Right (Left err, symtbl', ts') -> Right ((Just (Syn_var_decl var_id var_ty), symtbl', ts'), err)
                            )
                   _ -> return $ Right ((Just (Syn_var_decl var_id var_ty), symtbl, tokens), [])
                )
      case r of
        Left err -> throwE err
        Right r' -> return r'
    _ -> let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
         in
           throwE (Error_Excep Excep_assert_failed loc)


{- par_fun_decl' :: Symtbl -> Syntree_node -> [Tk_code] -> ((Syntree_node, Symtbl, [Tk_code]), [Error_codes])
par_fun_decl' symtbl fun tokens =
  let par_fun_type tokens = case tokens of
                              Tk_typed_as:ts -> (case par_type_decl tokens  of
                                                   (Right ty, ts') -> ((ty, ts'), [])
                                                   (Left err, ts') -> ((Ty_abs, ts'), err)
                                                )
                              _ -> ((Ty_abs, tokens), [])
  in
    case fun of
      Syn_fun_decl' fun_id args fun_body (Ty_env binds, fun_ty) ->
        (case tokens of
           Tk_L_par:Tk_R_par:ts -> ((Syn_fun_decl' fun_id args fun_body (Ty_env binds, fun_ty'), symtbl, tokens'), errs)
             where
               ((fun_ty', tokens'), errs) = par_fun_type ts
           Tk_L_par:ts -> let ((args', ts'), symtbl', arg_errs) = par_args symtbl ts
                              {- binds' = Prelude.map snd $ Prelude.foldl (\bs -> \(a_id, _) -> case Prelude.lookup a_id bs of
                                                                                               Just b -> Set.toList $ Set.difference (Set.fromList bs) (Set.fromList [(a_id, b)])
                                                                                               Nothing -> bs
                                                                       ) (Prelude.map (\(id, ty) -> (id, (id, ty))) binds) (Prelude.map (\(Syn_var_decl a_id a_ty) -> (a_id, a_ty)) args') -}
                          in
                            case ts' of
                              Tk_R_par:ts'' -> ((Syn_fun_decl' fun_id (args ++ args') fun_body (Ty_env binds, fun_ty'), symtbl', tokens'), (arg_errs ++ fun_ty_errs))
                                where
                                  ((fun_ty', tokens'), fun_ty_errs) = par_fun_type ts''
                              _ -> ((Syn_fun_decl' fun_id (args ++ args') fun_body (Ty_env binds, fun_ty'), symtbl', tokens'), errs)
                                where
                                  ((fun_ty', tokens'), fun_ty_errs) = par_fun_type ts'
                                  errs = (arg_errs ++ [Imcomplete_function_declaration errmsg]) ++ fun_ty_errs
                                  errmsg = "missing closing R-blace in function declaration."
             where
               par_args :: Symtbl -> [Tk_code] -> (([Syntree_node], [Tk_code]), Symtbl, [Error_codes])
               par_args symtbl tokens =
                 case par_arg symtbl tokens of
                   ((Nothing, tokens'), symtbl', errs) -> (([], tokens'), symtbl', errs)
                   ((Just arg, tokens'), symtbl', errs) -> (case tokens' of
                                                              Tk_smcl:ts' -> ((arg:args, tokens''), symtbl'', (errs ++ errs'))
                                                                where
                                                                  ((args, tokens''), symtbl'', errs') = par_args symtbl' ts'
                                                              _ -> (([arg], tokens'), symtbl', errs)
                                                           )
               par_arg :: Symtbl -> [Tk_code] -> ((Maybe Syntree_node, [Tk_code]), Symtbl, [Error_codes])
               par_arg symtbl tokens =
                 case tokens of
                   (Tk_ident arg_id):ts ->
                     let arg = Syn_var arg_id Ty_abs
                     in
                       case cons_var_decl symtbl arg ts of
                         ((Nothing, symtbl', ts'), errs) -> ((Just (Syn_arg_decl arg_id Ty_abs), ts'), symtbl', errs)
                         ((Just (Syn_var_decl arg_id arg_ty), symtbl', ts'), errs) -> ((Just (Syn_arg_decl arg_id arg_ty), ts'), symtbl', errs)
                         ((Just wrong, symtbl', ts'), errs) -> assert False (let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                             in
                                                                               ((Just wrong, ts'), symtbl', (errs ++ [Internal_error errmsg]))
                                                                            )
                   _ -> ((Nothing, tokens), symtbl, [])
           
           _ -> ((Syn_fun_decl' fun_id args fun_body (Ty_env binds, fun_ty'), symtbl, tokens'), errs)
             where
               ((fun_ty', tokens'), fun_ty_errs) = par_fun_type tokens
               errs =  [Imcomplete_function_declaration errmsg] ++ fun_ty_errs
               errmsg = "missing opening L-blace in function declaration."
        )
      
      _ -> assert False (let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                         in
                            ((fun, symtbl, tokens), [Internal_error errmsg])
                        ) -}

par_fun_decl'1 :: Symtbl -> Syntree_node -> [Tk_code] -> ExceptT Error_Excep IO ((Syntree_node, Symtbl, [Tk_code]), [Error_codes])
par_fun_decl'1 symtbl fun tokens =
  let par_fun_type symtbl tokens =
        case tokens of
          Tk_typed_as:ts -> do
            r_ty <- runExceptT $ par_type_decl1 symtbl tokens
            return (case r_ty of
                      Left err -> Left err
                      Right (Right ty, symtbl', ts') -> Right ((ty, symtbl', ts'), [])
                      Right (Left err, symtbl', ts') -> Right ((Ty_abs, symtbl', ts'), err)
                   )
          _ -> return $ Right ((Ty_abs, symtbl, tokens), [])
  in
    case fun of
      Syn_fun_decl' fun_id args fun_body (Ty_env binds, fun_ty) ->
        case tokens of
          Tk_L_par:Tk_R_par:ts -> do
            r <- lift (do 
                          r_ty <- par_fun_type symtbl ts
                          return (case r_ty of
                                    Left err -> Left err
                                    Right ((fun_ty', symtbl', tokens'), errs) -> Right ((Syn_fun_decl' fun_id args fun_body (Ty_env binds, fun_ty'), symtbl', tokens'), errs)
                                 )
                      )
            case r of
              Left err -> throwE err
              Right r' -> return r'
          
          Tk_L_par:ts -> do
            r <- lift (do
                          r_args <- runExceptT $ par_args symtbl ts
                          case r_args of
                            Left err -> return $ Left err
                            Right ((args', symtbl', ts'), arg_errs) ->
                              (case ts' of
                                 Tk_R_par:ts'' -> do
                                   r_ty <- par_fun_type symtbl' ts''
                                   return (case r_ty of
                                             Left err -> Left err
                                             Right ((fun_ty', symtbl'', tokens'), ty_errs) ->
                                               Right ((Syn_fun_decl' fun_id (args ++ args') fun_body (Ty_env binds, fun_ty'), symtbl'', tokens'), (arg_errs ++ ty_errs))
                                          )
                                 _ -> do
                                   r_ty <- par_fun_type symtbl' ts'
                                   return (case r_ty of
                                             Left err -> Left err
                                             Right ((fun_ty', symtbl'', tokens'), ty_errs) ->
                                               Right ((Syn_fun_decl' fun_id (args ++ args') fun_body (Ty_env binds, fun_ty'), symtbl'', tokens'), errs)
                                               where
                                                 errmsg = "Missing closing R paren. in parameter declarator of function declaration."
                                                 errs = (arg_errs ++ [Imcomplete_function_declaration errmsg]) ++ ty_errs
                                          )
                              )
                      )
            case r of
              Left err -> throwE err
              Right r' -> return r'
              
              where
                par_args :: Symtbl -> [Tk_code] -> ExceptT Error_Excep IO (([Syntree_node], Symtbl, [Tk_code]), [Error_codes])
                par_args symtbl tokens = do
                  r <- lift (do
                                r_a <- runExceptT $ par_arg symtbl tokens
                                case r_a of
                                  Left err -> return $ Left err
                                  Right ((Nothing, symtbl', tokens'), errs) -> return $ Right (([], symtbl', tokens'), errs)
                                  Right ((Just arg, symtbl', tokens'), errs) ->
                                    (case tokens' of
                                       Tk_smcl:ts' -> do
                                         r_as <- runExceptT $ par_args symtbl' ts'
                                         return (case r_as of
                                                   Left err -> Left err
                                                   Right ((args, symtbl'', tokens''), errs') -> Right ((arg:args, symtbl'', tokens''), (errs ++ errs'))
                                                )
                                       _ -> return $ Right (([arg], symtbl', tokens'), errs)
                                    )
                            )
                  case r of
                    Left err -> throwE err
                    Right r' -> return r'
                
                par_arg :: Symtbl -> [Tk_code] -> ExceptT Error_Excep IO ((Maybe Syntree_node, Symtbl, [Tk_code]), [Error_codes])
                par_arg symtbl tokens = do
                  r <- lift (case tokens of
                               (Tk_ident arg_id):ts -> do
                                 let arg = Syn_var arg_id Ty_abs
                                 r_arg <- runExceptT $ cons_var_decl1 symtbl arg ts
                                 return (case r_arg of
                                           Left err -> Left err
                                           Right ((Just (Syn_var_decl arg_id arg_ty), symtbl', ts'), errs) -> Right ((Just (Syn_arg_decl arg_id arg_ty), symtbl', ts'), errs)
                                           Right ((_, symtbl', ts'), errs) -> let loc  = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                              in
                                                                                Left (Error_Excep Excep_assert_failed loc)
                                        )
                               _ -> return $ Right ((Nothing, symtbl, tokens), [])
                            )
                  case r of
                    Left err -> throwE err
                    Right r' -> return r'
          
          _ -> do
            r <- lift (do
                          r_ty <- par_fun_type symtbl tokens
                          return (case r_ty of
                                    Left err -> Left err
                                    Right ((fun_ty', symtbl', tokens'), fun_ty_errs) -> Right ((Syn_fun_decl' fun_id args fun_body (Ty_env binds, fun_ty'), symtbl', tokens'), errs)
                                      where
                                        errmsg = "Missing parameter declaration at top level declarator of function declaration."
                                        errs =  [Imcomplete_function_declaration errmsg] ++ fun_ty_errs
                                 )
                      )
            case r of
              Left err -> throwE err
              Right r' -> return r'
      
      _ -> let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
           in
             throwE (Error_Excep Excep_assert_failed loc)


{- cons_fun_tree' symtbl fun tokens =
  case fun of
    --Syn_fun_decl fun_id args fun_body fun_ty ->
    Syn_fun_decl' fun_id args fun_body (env, fun_ty) ->
      case par_fun_decl' symtbl fun tokens of
        --((Syn_fun_decl fun_id' args' fun_body' fun_ty', symtbl', tokens'), errs) ->
        ((Syn_fun_decl' fun_id' args' fun_body' (env'@(Ty_env binds), fun_ty'), symtbl', tokens'), errs) ->
          assert (fun_id' == fun_id) (
            if tokens == [] then
              --((Syn_fun_decl fun_id' args' fun_body' fun_ty', symtbl', []), errs)
              ((Syn_fun_decl' fun_id' args' fun_body' (env', fun_ty'), symtbl', []), errs)
            else
              let (args'', errs') = case chk_args args' of
                                      (Right args'', errs_args) -> (args'', (Right errs):[(Right errs_args)])
                                      (Left args'', errs_args) -> (args'', (Right errs):[(Left errs_args)])
              in
                do
                  let (ts', errs_parse) = assert (tokens' /= []) (case tokens' of
                                                                    t':ts'' | t' == Tk_L_bra -> (ts'', Right [])
                                                                    t':ts'' -> (ts'', Left [Parse_error errmsg])
                                                                      where
                                                                        errmsg = "missing left brace to begin declaration of function body."
                                                                 )
                  --let fun' = Syn_fun_decl fun_id' args'' fun_body' fun_ty'
                  let fun' = Syn_fun_decl' fun_id' args'' fun_body' (env', fun_ty')
                  let (symtbl'', err_funreg) = sym_regist False symtbl' Sym_cat_decl (fun_id', fun')
                  let (new_scope, errs_argreg) = Prelude.foldl (\(sytbl, errs) -> \arg@(Syn_arg_decl id _) -> case sym_regist False sytbl Sym_cat_decl (id, arg) of
                                                                                                                (sytbl', Just err_reg) -> (sytbl', (errs ++ [err_reg]))
                                                                                                                (sytbl', Nothing) -> (symtbl', errs)
                                                               ) ((sym_enter_scope (Just symtbl'') Sym_cat_decl), []) args''
                  let errs0 = errs' ++ [errs_parse] ++ [(mkup_errs err_funreg)] ++ [(Right errs_argreg)]
                  case fun_body' of
                    (Syn_scope ([], Syn_none)) -> let (((Ty_env binds', var_decls), expr_par_trees), new_scope', ts'', errs_body) = parse_fun_body new_scope env' ts'
                                                      binds'' = Prelude.map snd (Prelude.foldl (\bs -> \(a_id, _) -> case Prelude.lookup a_id bs of
                                                                                                   Just b -> Set.toList $ Set.difference (Set.fromList bs) (Set.fromList [(a_id, b)])
                                                                                                   Nothing -> bs
                                                                                               )
                                                                                  (Prelude.map (\(id, ty) -> (id, (id, ty))) binds')
                                                                                  (Prelude.map (\(Syn_arg_decl a_id a_ty) -> (a_id, a_ty)) args'')
                                                                                )
                                                      --((var_decls, expr_par_trees), new_scope', ts'', errs_body) = parse_fun_body new_scope ts'
                                                      fun_body'' = (var_decls, (case expr_par_trees of
                                                                                  [] -> Syn_none
                                                                                  [e] -> e
                                                                                  es -> Syn_expr_seq es Ty_abs
                                                                               )
                                                                   )
                                                      --fun'' = Syn_fun_decl fun_id' args'' (Syn_scope fun_body'') fun_ty'
                                                      fun'' = Syn_fun_decl' fun_id' args'' (Syn_scope fun_body'') (Ty_env binds'', fun_ty')
                                                      errs1 = errs0 ++ [(Right errs_body)]
                                                  in
                                                    let prev_scope = sym_leave_scope new_scope' Sym_cat_decl
                                                        (prev_scope', err_funreg') = if (sym_crnt_level (sym_decl prev_scope)) <= 1 then
                                                                                       sym_regist False prev_scope Sym_cat_func (fun_id', fun'')
                                                                                     else
                                                                                       (prev_scope, Nothing)
                                                        errs1' = errs1 ++ [(mkup_errs err_funreg')]
                                                        errmsg = "missing right brace to end declaration of function body."
                                                    in
                                                      case cat_errs (fun'', errs1') of
                                                        (Right r, errs'') -> (case ts'' of
                                                                                Tk_R_bra:tokens'' -> ((r, prev_scope', tokens''), errs'')
                                                                                _ -> ((r, prev_scope', ts''), (errs'' ++ [Parse_error errmsg]))
                                                                             )
                                                        (Left r, errs'') -> (case ts'' of
                                                                               Tk_R_bra:tokens'' -> ((r, prev_scope', tokens''), errs'')
                                                                               _ -> ((r, prev_scope', ts''), (errs'' ++ [Parse_error errmsg]))
                                                                            )
                    
                    _ -> assert False (let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                       in
                                         ((r, new_scope, ts'), (errs'' ++ [Internal_error errmsg]))
                                      )
                      where
                        (r, errs'') = case cat_errs (fun', errs0) of
                                        (Right r', errs0') -> (r', errs0')
                                        (Left r', errs0') -> (r', errs0')
            )
          where
            mkup_errs :: (Maybe Error_codes) -> Either [Error_codes] [Error_codes]
            mkup_errs err =
              case err of
                Just err' -> Right [err']
                Nothing -> Right []
            
            cat_errs :: (Syntree_node, [Either [Error_codes] [Error_codes]]) -> (Either Syntree_node Syntree_node, [Error_codes])
            cat_errs (syntree, errs) =
              case errs of
                [] -> (Right syntree, [])
                _ -> let r = Prelude.foldl (\acc -> \es -> (do
                                                               (done, yet) <- acc
                                                               assert (yet /= []) (
                                                                 case yet of
                                                                   y:yet' -> assert (y == es) (
                                                                     case es of
                                                                       Right es' -> Right ((done ++ es'), yet')
                                                                       Left es' -> Left (done, yet)
                                                                     )
                                                                 )
                                                           )
                                           ) (Right ([], errs)) errs
                     in
                       case r of
                         Right (errs', remains) -> assert (remains == []) (Right syntree, errs')
                         Left (errs', remains) -> (Left syntree, (errs' ++ remains'))
                           where
                             remains' = Prelude.foldl (\acc -> \es -> case es of
                                                                        Right es' -> (acc ++ es')
                                                                        Left es' -> (acc ++ es')
                                                      ) [] remains
            
            chk_args :: [Syntree_node] -> (Either [Syntree_node] [Syntree_node], [Error_codes])
            chk_args args =
              let chk_decls (as, omits) =
                    case as of
                      [] -> (Right [], [])
                      [a] -> (Right [(snd a)], [])
                      a:as' -> (case Prelude.lookup (fst a) omits of
                                  Just _ -> chk_decls (as', omits)
                                  Nothing -> (case Prelude.lookup (fst a) as' of
                                                Nothing -> (case chk_decls (as', omits) of
                                                              (Right as'', errs) -> (Right ((snd a) : as''), errs)
                                                              (Left as'', errs) ->  (Left ((snd a) : as''), errs)
                                                           )
                                                Just a' -> (case chk_decls (as', (a:omits)) of
                                                              (Right as'', errs) -> (Left ((snd a) : as''), ((Symbol_redefinition errmsg) : errs))
                                                              (Left ill_decls, errs) -> (Left ((snd a) : ill_decls), ((Symbol_redefinition errmsg) : errs))
                                                           )
                                                  where
                                                    errmsg = "redefinition of " ++ (show $ fst a) ++ " in function arguments."
                                             )
                               )
              in
                chk_decls (args', [])
              where
                args' = Prelude.foldl (\as -> \a -> case a of
                                          (Syn_arg_decl id _) -> as ++ [(id, a)]
                                          _ -> assert False as
                                      ) [] args
            
            merge_env' :: Ty_env -> Ty_env -> Ty_env
            merge_env' env1 env2 =
              case env1 of
                Ty_env [] -> env2
                Ty_env env1' -> (case env2 of
                                   Ty_env [] -> env1
                                   Ty_env env2' -> Ty_env $ concat [env1', env2']
                                )
            parse_fun_body :: Symtbl -> Ty_env -> [Tk_code] -> (((Ty_env, [Syntree_node]), [Syntree_node]), Symtbl, [Tk_code], [Error_codes])
            parse_fun_body symtbl contex tokens =
              case cons_ptree symtbl tokens (False, True, True) of
                --(Just fun_decl@(Syn_fun_decl fun_id args fun_body fun_ty), symtbl', tokens') ->
                (Just fun_decl@(Syn_fun_decl' fun_id args fun_body (env0, fun_ty)), symtbl', tokens') ->
                  (case tokens' of
                     [] -> (((env, [fun_decl]), []), symtbl', [], [])
                     _ -> let (((env1, var_decls), expr_trees), symtbl'', tokens'', errs) = parse_fun_body symtbl' contex tokens'
                          in
                            ((((merge_env' env0 env1), fun_decl:var_decls), expr_trees), symtbl'', tokens'', errs)
                  )
                (Just var_decl@(Syn_var_decl _ _), symtbl', tokens') ->
                  (case tokens' of
                     [] -> (((Ty_env [], [var_decl]), []), symtbl', [], [Parse_error errmsg])
                     Tk_smcl:ts' -> let (((env1, var_decls), expr_trees), symtbl'', tokens'', errs) = parse_fun_body symtbl' contex ts'
                                    in
                                      (((env1, var_decl:var_decls), expr_trees), symtbl'', tokens'', errs)
                     _ -> let (((env1, var_decls), expr_trees), symtbl'', tokens'', errs) = parse_fun_body symtbl' contex tokens'
                          in
                            (((env1, var_decl:var_decls), expr_trees), symtbl'', tokens'', (Parse_error errmsg):errs)
                  )
                  where
                    errmsg = "missing semicolon at the end of declaration."
                (Just expr_par_tree, symtbl', tokens') ->
                  (case tokens' of
                     [] -> (((Ty_env [], []), [expr_par_tree]), symtbl', [], [Parse_error errmsg])
                     Tk_smcl:ts' -> let (((env1, var_decls), expr_trees), symtbl'', tokens'', errs) = parse_fun_body symtbl' contex ts'
                                    in
                                      (((env1, var_decls), expr_par_tree:expr_trees), symtbl'', tokens'', errs)
                     _ -> let (((env1, var_decls), expr_trees), symtbl'', tokens'', errs) = parse_fun_body symtbl' contex tokens'
                          in
                            (((env1, var_decls), expr_par_tree:expr_trees), symtbl'', tokens'', (Parse_error errmsg):errs)
                  )
                  where
                    errmsg = "missing semicolon at the end of semtence."
                (Nothing, symtbl', tokens') -> (((Ty_env [], []), []), symtbl', tokens', [])
                
        ((wrong, symtbl', tokens'), errs) -> assert False (let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                           in
                                                             ((wrong, symtbl', tokens'), (errs ++ [Internal_error errmsg]))
                                                          )
    _ -> assert False (let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                       in
                         ((fun, symtbl, tokens), [Internal_error errmsg])
                      ) -}

cons_fun_tree'1 :: Symtbl -> Syntree_node -> [Tk_code] -> ExceptT Error_Excep IO ((Syntree_node, Symtbl, [Tk_code]), [Error_codes])
cons_fun_tree'1 symtbl fun tokens =
  case fun of
    Syn_fun_decl' fun_id args fun_body (env, fun_ty) -> do
      r <- lift (do
                    r_decl <- runExceptT $ par_fun_decl'1 symtbl fun tokens
                    case r_decl of
                      Left err -> return $ Left err
                      Right ((fun@(Syn_fun_decl' fun_id' args' fun_body' (env'@(Ty_env binds), fun_ty')), symtbl', tokens'), errs) ->
                        if fun_id' /= fun_id then (do
                                                      let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                      return $ Left (Error_Excep Excep_assert_failed loc)
                                                  )
                        else
                          do
                            case tokens' of
                              [] -> return $ Right ((Syn_fun_decl' fun_id' args' fun_body' (env', fun_ty'), symtbl', []), errs'')
                                where
                                  errmsg = "Function declaration has no body at top level declarator."
                                  errs'' = errs ++ [Imcomplete_function_declaration errmsg]
                              _ -> (do
                                       r_args <- runExceptT $ exam_redef (fun:args')
                                       case r_args of
                                         Left err -> return $ Left err
                                         Right (args0, errs_args) -> do
                                           let args'' = Prelude.foldl (\as -> \a -> (case a of
                                                                                       Syn_arg_decl _ _ -> as ++ [a]
                                                                                       _ -> as
                                                                                    )
                                                                      ) [] args0
                                           let (ts', errs_parse) = case tokens' of
                                                                     Tk_L_bra:ts'' -> (ts'', [])
                                                                     t':ts'' -> (tokens', [Imcomplete_function_declaration errmsg])
                                                                       where
                                                                         errmsg = "Missing beginning L brace for declaration of function body."
                                           
                                           let (symtbl'', err_funreg) = sym_regist False symtbl' Sym_cat_decl (fun_id', (Syn_fun_decl' fun_id' args'' fun_body' (env', fun_ty')))
                                           let lv_before = sym_crnt_level (sym_decl symtbl'')
                                           let (new_scope, errs_argreg) =
                                                 Prelude.foldl (\(stbl, es) -> \arg@(Syn_arg_decl id _) -> case sym_regist False stbl Sym_cat_decl (id, arg) of
                                                                                                             (stbl', Just err_reg) -> (stbl', (es ++ [err_reg]))
                                                                                                             (stbl', Nothing) -> (stbl', es)
                                                               ) ((sym_enter_scope (Just symtbl'') Sym_cat_decl), []) args''
                                           
                                           let errs0 = errs ++ errs_args ++ errs_parse ++ (case err_funreg of
                                                                                             Just e -> [e]
                                                                                             Nothing -> []
                                                                                          ) ++ errs_argreg
                                           case fun_body' of
                                             (Syn_scope ([], Syn_none)) -> do
                                               r_body <- runExceptT $ parse_fun_body new_scope args'' ts'
                                               case r_body of
                                                 Left err -> return $ Left err
                                                 Right (((Ty_env binds', decls), stmts), new_scope', ts'', errs_body) ->
                                                   do
                                                     {- let binds'' = Prelude.map snd (Prelude.foldl (\bs -> \(a_id, _) -> case Prelude.lookup a_id bs of
                                                                                                      Just b -> Set.toList $ Set.difference (Set.fromList bs) (Set.fromList [(a_id, b)])
                                                                                                      Nothing -> bs
                                                                                                  )
                                                                                     (Prelude.map (\(id, ty) -> (id, (id, ty))) binds') (Prelude.map (\(Syn_arg_decl a_id a_ty) -> (a_id, a_ty)) args'')
                                                                                   ) -}
                                                     let decls' = Prelude.foldl (\ds -> \d -> (case d of
                                                                                                 Syn_arg_decl _ _ -> ds
                                                                                                 _ -> ds ++ [d]
                                                                                              )
                                                                                ) [] decls
                                                     let fun_body'' = Syn_scope (decls', (case stmts of
                                                                                           [] -> Syn_none
                                                                                           [e] -> e
                                                                                           es -> Syn_expr_seq es Ty_abs
                                                                                        )
                                                                                )
                                                     let fun'' = Syn_fun_decl' fun_id' args'' fun_body'' (Ty_env binds', fun_ty')
                                                     
                                                     let prev_scope = sym_leave_scope new_scope' Sym_cat_decl
                                                     if sym_crnt_level (sym_decl prev_scope) /= lv_before then let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                                                               in
                                                                                                                 return $ Left (Error_Excep Excep_assert_failed loc)
                                                       else
                                                       do
                                                         let (prev_scope', err_funreg') = sym_regist (case err_funreg of
                                                                                                        Just (Symbol_redefinition _) -> False
                                                                                                        _ -> True
                                                                                                     ) prev_scope Sym_cat_func (fun_id', fun'')
                                                         let errs1 = errs0 ++ errs_body ++ (case err_funreg' of
                                                                                              Just e -> [e]
                                                                                              Nothing -> []
                                                                                           )
                                                         return (case ts'' of
                                                                   Tk_R_bra:tokens'' -> Right ((fun'', prev_scope', tokens''), errs1)
                                                                   _ -> Right ((fun'', prev_scope', ts''), (errs1 ++ [Imcomplete_function_declaration errmsg]))
                                                                     where
                                                                       errmsg = "Missing R brace to end up declaration of function body."
                                                                )
                                           
                                             _ -> let loc  = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                  in
                                                    return $ Left (Error_Excep Excep_assert_failed loc)
                                   )
                )
      case r of
        Left err -> throwE err
        Right r' -> return r'
    
    _ -> let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
         in
           throwE (Error_Excep Excep_assert_failed loc)


exam_redef :: [Syntree_node] -> ExceptT Error_Excep IO ([Syntree_node], [Error_codes])
exam_redef args =
  let chk_decls (as, omits) =
        case as of
          [] -> (Right [], [])
          [a] -> (Right [(snd a)], [])
          a:as' -> (case Prelude.lookup (fst a) omits of
                      Just _ -> chk_decls (as', omits)
                      Nothing -> (case Prelude.lookup (fst a) as' of
                                    Nothing -> (case chk_decls (as', omits) of
                                                  (Right as'', errs) -> (Right ((snd a) : as''), errs)
                                                  (Left as'', errs) ->  (Left ((snd a) : as''), errs)
                                               )
                                    Just a' -> (case chk_decls (as', (a:omits)) of
                                                  (Right as'', errs) -> (Left ((snd a) : as''), ((Symbol_redefinition errmsg) : errs))
                                                  (Left as'', errs) -> (Left ((snd a) : as''), ((Symbol_redefinition errmsg) : errs))
                                               )
                                      where
                                        errmsg = "Redefinition of " ++ (show $ fst a) ++ " in function arguments declaration."
                                 )
                   )
  in
    do
      args' <- lift $ Prelude.foldl (\as -> \a -> (do
                                                      as' <- as
                                                      case as' of
                                                        Left err -> return (Left err)
                                                        Right as'' -> return (case a of
                                                                                (Syn_fun_decl' id _ _ _) -> Right (as'' ++ [(id, a)])
                                                                                (Syn_arg_decl id _) -> Right (as'' ++ [(id, a)])
                                                                                (Syn_var_decl id _) -> Right (as'' ++ [(id, a)])
                                                                                _ -> let loc  = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                                     in
                                                                                       Left (Error_Excep Excep_assert_failed loc)
                                                                             )
                                                  )
                                    ) (return (Right [])) args
      case args' of
        Left err -> throwE err
        Right as' -> return (case chk_decls (as', []) of
                               (Right as'', errs_args) -> (as'', errs_args)
                               (Left as'', errs_args) -> (as'', errs_args)
                            )

parse_fun_body :: Symtbl -> [Syntree_node] -> [Tk_code] -> ExceptT Error_Excep IO (((Ty_env, [Syntree_node]), [Syntree_node]), Symtbl, [Tk_code], [Error_codes])
parse_fun_body symtbl decls tokens = do
  r <- lift (do
                r_body <- runExceptT $ cons_ptree1 symtbl tokens (False, True, True)
                case r_body of
                  Left err -> return $ Left err
                  Right body -> do
                    case body of
                      (Nothing, symtbl', tokens') -> return $ Right (((Ty_env [], decls), []), symtbl', tokens', [])
                      
                      (Just fun_decl@(Syn_fun_decl' fun_id args fun_body (env0, fun_ty)), symtbl', tokens') -> do
                        r_decls <- runExceptT $ exam_redef (decls ++ [fun_decl])
                        case r_decls of
                          Left err -> return $ Left err
                          Right (decls', err_decl) -> (case tokens' of
                                                         [] -> return $ Right (((env0, decls'), []), symtbl', [], err_decl)
                                                         _ -> do
                                                           r_body' <- runExceptT $ parse_fun_body symtbl' decls' tokens'
                                                           return (case r_body' of
                                                                     Left err -> Left err
                                                                     Right (((env1, decls''), exprs), symtbl'', tokens'', errs) ->
                                                                       Right ((((ty_ovwt_env env0 env1), decls''), exprs), symtbl'', tokens'', (err_decl ++ errs))
                                                                  )
                                                      )
                      
                      (Just var_decl@(Syn_var_decl _ _), symtbl', tokens') -> do
                        r_decls <- runExceptT $ exam_redef (decls ++ [var_decl])
                        case r_decls of
                          Left err -> return $ Left err
                          Right (decls', err_decl) -> (case tokens' of
                                                         [] -> return $ Right (((Ty_env [], decls'), []), symtbl', [], (err_decl ++ [Parse_error errmsg]))
                                                         Tk_smcl:ts' -> do
                                                           r_body' <- runExceptT $ parse_fun_body symtbl' decls' ts'
                                                           return (case r_body' of
                                                                     Left err -> Left err
                                                                     Right (((env1, decls''), exprs), symtbl'', tokens'', errs) ->
                                                                       Right (((env1, decls''), exprs), symtbl'', tokens'', (err_decl ++ errs))
                                                                  )
                                                         _ -> do
                                                           r_body' <- runExceptT $ parse_fun_body symtbl' decls' tokens'
                                                           return (case r_body' of
                                                                     Left err -> Left err
                                                                     Right (((env1, decls''), exprs), symtbl'', tokens'', errs) ->
                                                                       Right (((env1, decls''), exprs), symtbl'', tokens'', (err_decl ++ (Parse_error errmsg):errs))
                                                                  )
                                                      )
                        where
                          errmsg = "missing semicolon at the end of declaration."
                      
                      (Just expr, symtbl', tokens') ->
                        (case tokens' of
                           [] -> return $ Right (((Ty_env [], decls), [expr]), symtbl', [], [Parse_error errmsg])
                           Tk_smcl:ts' -> do
                             r_body' <- runExceptT $ parse_fun_body symtbl' decls ts'
                             return (case r_body' of
                                       Left err -> Left err
                                       Right (((env1, decls'), exprs), symtbl'', tokens'', errs) -> Right (((env1, decls'), expr:exprs), symtbl'', tokens'', errs)
                                    )
                           
                           _ -> do
                             r_body' <- runExceptT $ parse_fun_body symtbl' decls tokens'
                             return (case r_body' of
                                       Left err -> Left err
                                       Right (((env1, decls'), exprs), symtbl'', tokens'', errs) -> Right (((env1, decls'), expr:exprs), symtbl'', tokens'', (Parse_error errmsg):errs)
                                    )
                        )
                        where
                          errmsg = "missing semicolon at the end of semtence."
                      
                      (_, symtbl', tokens') -> let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                               in
                                                 return $ Left (Error_Excep Excep_assert_failed loc)
            )
  case r of
    Left err -> throwE err
    Right r' -> return r'


{- par_fun_decl :: Symtbl -> Syntree_node -> [Tk_code] -> ((Syntree_node, Symtbl, [Tk_code]), [Error_codes])
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
                                                                             in
                                                                               ((fun_decl, symtbl, tokens'), errs)
                                                     Tk_L_par:ts -> let ((args', ts'), symtbl', arg_errs) = cons_args_decl symtbl ts
                                                                    in
                                                                      case ts' of
                                                                        Tk_R_par:ts'' -> let fun_decl = Syn_fun_decl fun_id (args ++ args') fun_body fun_ty'
                                                                                         in
                                                                                           ((fun_decl, symtbl', tokens'), errs)
                                                                          where
                                                                            ((fun_ty', tokens'), fun_ty_errs) = par_fun_type ts''
                                                                            errs = arg_errs ++ fun_ty_errs
                                                                        
                                                                        _ -> let fun_decl = Syn_fun_decl fun_id (args ++ args') fun_body fun_ty'
                                                                             in
                                                                               ((fun_decl, symtbl', tokens'), errs)
                                                                          where
                                                                            ((fun_ty', tokens'), fun_ty_errs) = par_fun_type ts'
                                                                            errs = arg_errs ++ [Imcomplete_function_declaration errmsg] ++ fun_ty_errs
                                                                            errmsg = "missing closing R-blace in function declaration."
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
                                                                   ((Nothing, symtbl', ts'), errs) -> (Just (Syn_arg_decl arg_id Ty_abs, ts'), symtbl', errs)
                                                                   ((Just (Syn_var_decl arg_id arg_ty), symtbl', ts'), errs) -> (Just (Syn_arg_decl arg_id arg_ty, ts'), symtbl', errs)
                                                                   ((_, symtbl', ts'), errs) -> (Just (Syn_none, ts'), symtbl', errs)
                                                             _ -> (Nothing, symtbl, [])
                                                         
                                                         
                                                     _ -> let fun_decl = Syn_fun_decl fun_id args fun_body fun_ty'
                                                          in
                                                            ((fun_decl, symtbl, tokens'), errs)
                                                       where
                                                         ((fun_ty', tokens'), fun_ty_errs) = par_fun_type tokens
                                                         errs =  [Imcomplete_function_declaration errmsg] ++ fun_ty_errs
                                                         errmsg = "missing opening L-blace in function declaration."
                                                  )
      
      _ -> ((Syn_none, symtbl, tokens), [Internal_error "Calling cons_var_decl with non variable constructor."])

cons_fun_tree symtbl fun tokens =
  case fun of
    --Syn_fun_decl' fun_id args fun_body (env, fun_ty) ->
    Syn_fun_decl fun_id args fun_body fun_ty ->
      case par_fun_decl symtbl fun tokens of
        --((Syn_fun_decl' fun_id' args' fun_body' (env', fun_ty'), symtbl', tokens'), errs) ->
        ((Syn_fun_decl fun_id' args' fun_body' fun_ty', symtbl', tokens'), errs) ->
          assert (fun_id' == fun_id') (
            if tokens == [] then
              --((Syn_fun_decl' fun_id' args' fun_body' (env', fun_ty'), symtbl', []), errs)
              ((Syn_fun_decl fun_id' args' fun_body' fun_ty', symtbl', []), errs)
            else
              let (args'', errs') = case chk_args args' of
                                      (Right args'', errs_args) -> (args'', (Right errs):[(Right errs_args)])
                                      (Left args'', errs_args) -> (args'', (Right errs):[(Left errs_args)])
              in
                do
                  let (ts', errs_parse) = assert (tokens' /= []) (case tokens' of
                                                                    t':ts'' | t' == Tk_L_bra -> (ts'', Right [])
                                                                    t':ts'' -> (ts'', Left [Parse_error errmsg])
                                                                      where
                                                                        errmsg = "missing left brace to begin declaration of function body."
                                                                 )
                  --let fun' = Syn_fun_decl' fun_id' args'' fun_body' (env', fun_ty')
                  let fun' = Syn_fun_decl fun_id' args'' fun_body' fun_ty'
                  let (symtbl'', err_funreg) = sym_regist False symtbl' Sym_cat_decl (fun_id', fun')
                  let (new_scope, errs_argreg) = Prelude.foldl (\(sytbl, errs) -> \arg@(Syn_arg_decl id _) -> case sym_regist False sytbl Sym_cat_decl (id, arg) of
                                                                                                                (sytbl', Just err_reg) -> (sytbl', (errs ++ [err_reg]))
                                                                                                                (sytbl', Nothing) -> (symtbl', errs)
                                                               ) ((sym_enter_scope (Just symtbl'') Sym_cat_decl), []) args''
                  let errs0 = errs' ++ [errs_parse] ++ [(mkup_errs err_funreg)] ++ [(Right errs_argreg)]
                  case fun_body' of
                    (Syn_scope ([], Syn_none)) -> let ((var_decls, expr_par_trees), new_scope', ts'', errs_body) = parse_fun_body new_scope ts'
                                                      fun_body'' = (var_decls, (case expr_par_trees of
                                                                                  [] -> Syn_none
                                                                                  [e] -> e
                                                                                  es -> Syn_expr_seq es Ty_abs
                                                                               )
                                                                   )
                                                      --fun'' = Syn_fun_decl' fun_id' args'' (Syn_scope fun_body'') (env',fun_ty')
                                                      fun'' = Syn_fun_decl fun_id' args'' (Syn_scope fun_body'') fun_ty'
                                                      errs1 = errs0 ++ [(Right errs_body)]
                                                  in
                                                    let prev_scope = sym_leave_scope new_scope' Sym_cat_decl
                                                        (prev_scope', err_funreg') = if (sym_crnt_level (sym_decl prev_scope)) <= 1 then
                                                                                       sym_regist False prev_scope Sym_cat_func (fun_id', fun'')
                                                                                     else
                                                                                       (prev_scope, Nothing)
                                                        errs1' = errs1 ++ [(mkup_errs err_funreg')]
                                                        errmsg = "missing right brace to end declaration of function body."
                                                    in
                                                      case cat_errs (fun'', errs1') of
                                                        (Right r, errs'') -> (case ts'' of
                                                                                Tk_R_bra:tokens'' -> ((r, prev_scope', tokens''), errs'')
                                                                                _ -> ((r, prev_scope', ts''), (errs'' ++ [Parse_error errmsg]))
                                                                             )
                                                        (Left r, errs'') -> (case ts'' of
                                                                               Tk_R_bra:tokens'' -> ((r, prev_scope', tokens''), errs'')
                                                                               _ -> ((r, prev_scope', ts''), (errs'' ++ [Parse_error errmsg]))
                                                                            )
                    
                    _ -> assert False (let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                       in
                                         ((r, new_scope, ts'), (errs'' ++ [Internal_error errmsg]))
                                      )
                      where
                        (r, errs'') = case cat_errs (fun', errs0) of
                                        (Right r', errs0') -> (r', errs0')
                                        (Left r', errs0') -> (r', errs0')
            )
          where
            mkup_errs :: (Maybe Error_codes) -> Either [Error_codes] [Error_codes]
            mkup_errs err =
              case err of
                Just err' -> Right [err']
                Nothing -> Right []
            
            cat_errs :: (Syntree_node, [Either [Error_codes] [Error_codes]]) -> (Either Syntree_node Syntree_node, [Error_codes])
            cat_errs (syntree, errs) =
              case errs of
                [] -> (Right syntree, [])
                _ -> let r = Prelude.foldl (\acc -> \es -> (do
                                                               (done, yet) <- acc
                                                               assert (yet /= []) (
                                                                 case yet of
                                                                   y:yet' -> assert (y == es) (
                                                                     case es of
                                                                       Right es' -> Right ((done ++ es'), yet')
                                                                       Left es' -> Left (done, yet)
                                                                     )
                                                                 )
                                                           )
                                           ) (Right ([], errs)) errs
                     in
                       case r of
                         Right (errs', remains) -> assert (remains == []) (Right syntree, errs')
                         Left (errs', remains) -> (Left syntree, (errs' ++ remains'))
                           where
                             remains' = Prelude.foldl (\acc -> \es -> case es of
                                                                        Right es' -> (acc ++ es')
                                                                        Left es' -> (acc ++ es')
                                                      ) [] remains
            
            chk_args :: [Syntree_node] -> (Either [Syntree_node] [Syntree_node], [Error_codes])
            chk_args args =
              let chk_decls (as, omits) =
                    case as of
                      [] -> (Right [], [])
                      [a] -> (Right [(snd a)], [])
                      a:as' -> (case Prelude.lookup (fst a) omits of
                                  Just _ -> chk_decls (as', omits)
                                  Nothing -> (case Prelude.lookup (fst a) as' of
                                                Nothing -> (case chk_decls (as', omits) of
                                                              (Right as'', errs) -> (Right ((snd a) : as''), errs)
                                                              (Left as'', errs) ->  (Left ((snd a) : as''), errs)
                                                           )
                                                Just a' -> (case chk_decls (as', (a:omits)) of
                                                              (Right as'', errs) -> (Left ((snd a) : as''), ((Symbol_redefinition errmsg) : errs))
                                                              (Left ill_decls, errs) -> (Left ((snd a) : ill_decls), ((Symbol_redefinition errmsg) : errs))
                                                           )
                                                  where
                                                    errmsg = "redefinition of " ++ (show $ fst a) ++ " in function arguments."
                                             )
                               )
              in
                chk_decls (args', [])
              where
                args' = Prelude.foldl (\as -> \a -> case a of
                                          (Syn_arg_decl id _) -> as ++ [(id, a)]
                                          _ -> assert False as
                                      ) [] args
            
            parse_fun_body :: Symtbl -> [Tk_code] -> (([Syntree_node], [Syntree_node]), Symtbl, [Tk_code], [Error_codes])
            parse_fun_body symtbl tokens =
              case cons_ptree symtbl tokens (False, True, True) of
                --(Just fun_decl@(Syn_fun_decl' fun_id args fun_body (env, fun_ty)), symtbl', tokens') ->
                (Just fun_decl@(Syn_fun_decl fun_id args fun_body fun_ty), symtbl', tokens') ->
                  (case tokens' of
                     [] -> (([fun_decl], []), symtbl', [], [])
                     _ -> let ((var_decls, expr_trees), symtbl'', tokens'', errs) = parse_fun_body symtbl' tokens'
                          in
                            ((fun_decl:var_decls, expr_trees), symtbl'', tokens'', errs)
                  )
                (Just var_decl@(Syn_var_decl _ _), symtbl', tokens') ->
                  (case tokens' of
                     [] -> (([var_decl], []), symtbl', [], [Parse_error errmsg])
                     Tk_smcl:ts' -> let ((var_decls, expr_trees), symtbl'', tokens'', errs) = parse_fun_body symtbl' ts'
                                    in
                                      ((var_decl:var_decls, expr_trees), symtbl'', tokens'', errs)
                     _ -> let ((var_decls, expr_trees), symtbl'', tokens'', errs) = parse_fun_body symtbl' tokens'
                          in
                            ((var_decl:var_decls, expr_trees), symtbl'', tokens'', (Parse_error errmsg):errs)
                  )
                  where
                    errmsg = "missing semicolon at the end of declaration."
                (Just expr_par_tree, symtbl', tokens') ->
                  (case tokens' of
                     [] -> (([], [expr_par_tree]), symtbl', tokens', [Parse_error errmsg])
                     Tk_smcl:ts' -> let ((var_decls, expr_trees), symtbl'', tokens'', errs) = parse_fun_body symtbl' ts'
                                    in
                                      ((var_decls, expr_par_tree:expr_trees), symtbl'', tokens'', errs)
                     _ -> let ((var_decls, expr_trees), symtbl'', tokens'', errs) = parse_fun_body symtbl' tokens'
                          in
                            ((var_decls, expr_par_tree:expr_trees), symtbl'', tokens'', (Parse_error errmsg):errs)
                  )
                  where
                    errmsg = "missing semicolon at the end of semtence."
                (Nothing, symtbl', tokens') -> (([], []), symtbl', tokens', [])
        
        ((wrong, symtbl', tokens'), errs) -> assert False (let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                           in
                                                             ((wrong, symtbl', tokens'), (errs ++ [Internal_error errmsg]))
                                                          )
    _ -> assert False (let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                       in
                         ((fun, symtbl, tokens), [Internal_error errmsg])
                      ) -}

{- cons_ptree :: Symtbl -> [Tk_code] -> (Bool, Bool, Bool) -> (Maybe Syntree_node, Symtbl, [Tk_code])
cons_ptree symtbl tokens (fun_declp, var_declp, par_contp) =
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
            Just ope' | ope' == Ope_asgn -> let right = cons_ptree symtbl tokens' (False, False, True)
                                            in
                                              case right of
                                                (Just right_expr, symtbl', tokens'') -> (Right (Syn_expr_asgn subexpr1 right_expr Ty_abs), symtbl', tokens'')
                                                (Nothing, symtbl', tokens'') -> (Left Illegal_left_expression_for_assignment, symtbl', tokens'')
            Just ope' | is_bin_op ope' -> let r2 = cons_ptree symtbl tokens' (False, False, True)
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
            _ -> let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                 in
                   (Left (Internal_error ("Unknow operator detecded in " ++ loc)), symtbl, tokens)
        
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
          Syn_expr_call fun_id app_args fun_ty -> (case tokens of
                                                     [] -> (Right fun_app, symtbl, [])
                                                     Tk_R_par:ts -> (Right fun_app, symtbl, tokens)
                                                     _ -> (case cons_ptree symtbl tokens (False, False, False) of
                                                             (Just expr, symtbl', tokens') ->
                                                               let arg = case expr of
                                                                           Syn_var v_id ty -> expr
                                                                           Syn_expr_call f_id f_args ty -> expr
                                                                           _ -> expr
                                                               in
                                                                 (case tokens' of
                                                                    Tk_comma:ts' ->
                                                                      (case (case par_fun_call symtbl' (Syn_expr_call fun_id [] fun_ty) ts' of
                                                                               (Right (Syn_expr_call _ args' _), stbl'', ts'') -> Right (arg:args', stbl'', ts'')
                                                                               (Left errs, stbl'', ts'') -> Left (errs, stbl'', ts'')
                                                                            ) of
                                                                         Right (app_args', symtbl'', tokens'') -> (Right (Syn_expr_call fun_id app_args' fun_ty), symtbl'', tokens'')
                                                                         Left (errs, symtbl'', tokens'') -> (Left errs, symtbl'', tokens'')
                                                                      )
                                                                    _ -> (Right (Syn_expr_call fun_id [arg] fun_ty), symtbl', tokens')
                                                                 )
                                                             (Nothing, symtbl', tokens') -> (Left [], symtbl', tokens')
                                                          )
                                                  )
          _ -> (Left [Internal_error "Calling cons_var_decl with non variable constructor."], symtbl, tokens)
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
        Tk_L_par:ts -> (case cons_ptree symtbl ts (False, False, True) of
                          (Just expr, symtbl', (Tk_R_par:ts')) -> cont_par symtbl' (Syn_expr_par expr (syn_node_typeof expr)) ts'
                          (_, symtbl',ts') -> (Nothing, symtbl', ts')
                       )
        Tk_if:ts ->
          (case cons_ptree symtbl ts (False, False, True) of
             (Just cond_expr, symtbl', (Tk_then:ts')) ->
               (case cons_ptree symtbl' ts' (False, False, True) of               
                  (Just true_expr, symtbl'_t, (t'':ts'')) | t'' == Tk_else -> (case cons_ptree symtbl'_t ts'' (False, False, True) of
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
              let fun = Syn_fun_decl' fun_id [] (Syn_scope ([], Syn_none)) (Ty_env [], Ty_abs)
                  --fun = Syn_fun_decl fun_id [] (Syn_scope ([], Syn_none)) Ty_abs
              in
                case cons_fun_tree' symtbl fun ts' of
                --case cons_fun_tree symtbl fun ts' of
                  --((fun'@(Syn_fun_decl fun_id' args' fun_body' fun_ty'), symtbl', tokens'), errs) -> (Just fun', symtbl', tokens')
                  ((fun'@(Syn_fun_decl' fun_id' args' fun_body' (env', fun_ty')), symtbl', tokens'), errs) -> (Just fun', symtbl', tokens')
                  ((_, symtbl', tokens'), errs) -> assert False (let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                 in
                                                                   (Nothing, symtbl', tokens')
                                                                )
                
                {- case par_fun_decl symtbl fun ts' of
                  ((fun@(Syn_fun_decl fun_id fun_args fun_body fun_ty), symtbl', (Tk_L_bra:ts'')), errs) -> do
                    let (symtbl'', err_funreg) = sym_regist False symtbl' Sym_cat_decl (fun_id, fun)
                    let (new_scope, errs_argreg) = Prelude.foldl (\(symtbl, errs) -> \arg@(Syn_arg_decl arg_id _) -> case sym_regist False symtbl Sym_cat_decl (arg_id, arg) of
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
                                                                                    [e] -> e
                                                                                    es -> Syn_expr_seq es Ty_abs
                                                                                )
                                                                    )
                                                        (fun', tokens') = (Syn_fun_decl fun_id fun_args (Syn_scope fun_body') fun_ty, us)
                                                        errs'' = errs' ++ errs_body
                                                    in
                                                      case tokens' of
                                                        Tk_R_bra:tokens'' -> let prev_scope = sym_leave_scope new_scope' Sym_cat_decl
                                                                             in                                                                              
                                                                               if (sym_crnt_level (sym_decl prev_scope)) <= 1 then
                                                                                 let (prev_scope', err_funreg') = sym_regist False prev_scope Sym_cat_func (fun_id, fun')
                                                                                 in
                                                                                   (Just fun', prev_scope', tokens'')
                                                                               else
                                                                                 (Just fun', prev_scope, tokens'')
                                                        _ -> (Nothing, new_scope', tokens')
                        where
                          parse_fun_body :: Symtbl -> [Tk_code] -> (([Syntree_node], [Syntree_node]), Symtbl, [Tk_code], [Error_codes])
                          parse_fun_body symtbl tokens =
                            case cons_ptree symtbl tokens (False, True, True) of
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
                      
                      _ -> assert False (let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                         in
                                           (Nothing, new_scope, ts')
                                        )
                  
                  ((_, symtbl',tokens'), errs) -> assert False (let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                in
                                                                  (Nothing, symtbl', tokens')
                                                               ) -}
            
            _ -> (Nothing, symtbl, ts)
          else (Nothing, symtbl, ts)
        Tk_var:ts -> if var_declp then
                       case ts of
                         (Tk_ident ident):ts' -> let var = Syn_var ident Ty_abs
                                                 in
                                                   case cons_var_decl symtbl var ts' of
                                                     --((Just var_decl, symtbl', tokens'), errs) -> (Just var_decl, symtbl', tokens')
                                                     ((Just (var_decl@(Syn_var_decl var_id var_ty)), symtbl', tokens'), errs) ->
                                                       let (symtbl'', err_symreg) = sym_regist False symtbl' Sym_cat_decl (var_id, var_decl)
                                                           errs' = (case err_symreg of
                                                                      Just e_reg  -> [e_reg]
                                                                      Nothing -> []
                                                                   ) ++ errs
                                                       in
                                                         (Just var_decl, symtbl'', tokens')
                                                     ((_, symtbl', tokens'), errs) -> (Nothing, symtbl', tokens')
                         _ -> (Nothing, symtbl, ts)
                     else
                       (Nothing, symtbl, ts)
        (Tk_ident ident):ts -> let var = Syn_var ident Ty_abs
                               in
                                 case ts of
                                   --tokens'@(t:ts') | not (is_op t) -> let fun_app = Syn_expr_call ident [] Ty_abs
                                   Tk_L_par:ts' ->
                                     let fun_app = Syn_expr_call ident [] Ty_abs
                                     in
                                       case par_fun_call symtbl fun_app ts' of
                                         (Right (fun_app'@(Syn_expr_call fun_id app_args app_ty)), symtbl', tokens') -> (case tokens' of
                                                                                                                           Tk_R_par:ts'' -> cont_par symtbl' fun_app' ts''
                                                                                                                           _ -> (Nothing, symtbl', tokens')
                                                                                                                        )
                                         (Left errs, symtbl', tokens') -> (Nothing, symtbl', tokens')
                                   _ -> cont_par symtbl var ts
                                 
                                 {- if var_declp then
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
                                   cont_par symtbl var ts -}
                                 
        _ -> (Nothing, symtbl, tokens) -}

cons_ptree1 :: Symtbl -> [Tk_code] -> (Bool, Bool, Bool) -> ExceptT Error_Excep IO (Maybe Syntree_node, Symtbl, [Tk_code])
cons_ptree1 symtbl tokens (fun_declp, var_declp, par_contp) =
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
      cons_expr symtbl subexpr1 tokens = do
        let (ope, tokens') = fetch_ope tokens
        case ope of
          Nothing -> return (Right subexpr1, symtbl, tokens)
          Just ope' | ope' == Ope_asgn -> do
                        r <- lift (do
                                      rhs <- runExceptT $ cons_ptree1 symtbl tokens' (False, False, True)
                                      case rhs of
                                        Left err -> return $ Left err
                                        Right (Just r_expr, symtbl', tokens'') -> return $ Right (Right (Syn_expr_asgn subexpr1 r_expr Ty_abs), symtbl', tokens'')
                                        Right (Nothing, symtbl', tokens'') -> return $ Right (Left Illegal_left_expression_for_assignment, symtbl', tokens'')
                                  )
                        case r of
                          Left err -> throwE err
                          Right r' -> return r'
          Just ope' | is_bin_op ope' -> do
                        r <- lift (do
                                      r2 <- runExceptT $ cons_ptree1 symtbl tokens' (False, False, True)
                                      case r2 of
                                        Left err -> return $ Left err
                                        Right (Just subexpr2, symtbl', tokens'') ->
                                          return $ Right (case subexpr2 of
                                                            Syn_val _ _ -> (Right (Syn_expr_bin ope' (subexpr1, subexpr2) Ty_abs), symtbl', tokens'')
                                                            Syn_var _ _ -> (Right (Syn_expr_bin ope' (subexpr1, subexpr2) Ty_abs), symtbl', tokens'')
                                                            Syn_expr_bin bin_ope (expr_1, expr_2) _ ->
                                                              if is_gte_op ope' bin_ope then
                                                                (Right (Syn_expr_bin bin_ope ((lm_im subexpr1 ope' expr_1), expr_2) Ty_abs), symtbl', tokens'')
                                                              else
                                                                (Right (Syn_expr_bin ope' (subexpr1, subexpr2) Ty_abs), symtbl', tokens'')
                                                            _ -> (Right (Syn_expr_bin ope' (subexpr1, subexpr2) Ty_abs), symtbl', tokens'')
                                                         )
                                        Right (Nothing, symtbl', tokens'') -> return $ Right (Left (Illegal_operands ope' Syn_none), symtbl', tokens'')
                                  )
                        case r of
                          Left err -> throwE err
                          Right r' -> return r'
          _ -> let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
               in
                 return (Left (Internal_error ("Unknown operator detecded in " ++ loc)), symtbl, tokens)
        
        where
          fetch_ope tokens = case tokens of
                               (Tk_asgn:ts) -> (Just Ope_asgn, ts)
                               (Tk_slash:ts) -> (Just Ope_div, ts)
                               (Tk_star:ts) -> (Just Ope_mul, ts)
                               (Tk_shaft:ts) -> (Just Ope_sub, ts)
                               (Tk_cross:ts) -> (Just Ope_add, ts)
                               _ -> (Nothing, tokens)
          lm_im expr_li bin_ope expr0 = -- Left-Most Inner-Most
            case expr0 of
              Syn_expr_bin ope_o (expr_o1@(Syn_val _ _), expr_o2) _ | is_gte_op bin_ope ope_o -> Syn_expr_bin ope_o ((Syn_expr_bin bin_ope (expr_li, expr_o1) Ty_abs), expr_o2) Ty_abs
              Syn_expr_bin ope_o (expr_o1@(Syn_var _ _), expr_o2) _ | is_gte_op bin_ope  ope_o -> Syn_expr_bin ope_o ((Syn_expr_bin bin_ope (expr_li, expr_o1) Ty_abs), expr_o2) Ty_abs
              Syn_expr_bin ope_o (expr_o1@(Syn_expr_bin ope_o1 _ _), expr_o2) _ | is_gte_op bin_ope ope_o -> Syn_expr_bin ope_o (lm_im expr_li bin_ope expr_o1, expr_o2) Ty_abs
              _ -> Syn_expr_bin bin_ope (expr_li, expr0) Ty_abs
      
      par_fun_call symtbl fun_app tokens = do
        r <- lift (case fun_app of
                     Syn_expr_call fun_id app_args fun_ty -> do
                       (case tokens of
                          [] -> return $ Right (Right fun_app, symtbl, [])
                          Tk_R_par:ts -> return $ Right (Right fun_app, symtbl, tokens)
                          _ -> do
                            r_a <- runExceptT $ cons_ptree1 symtbl tokens (False, False, False)
                            case r_a of
                              Left err -> return $ Left err
                              Right (Just expr, symtbl', tokens') -> do
                                let arg = case expr of
                                            Syn_var v_id ty -> expr
                                            Syn_expr_call f_id f_args ty -> expr
                                            _ -> expr
                                case tokens' of
                                  Tk_comma:ts' -> do
                                    r_as <- runExceptT $ par_fun_call symtbl' (Syn_expr_call fun_id [] fun_ty) ts'
                                    case r_as of
                                      Left err -> return r_as
                                      Right as' -> do
                                        r_as' <- return (case as' of
                                                           (Right (Syn_expr_call _ args' _), stbl'', ts'') -> Right (Right (arg:args'), stbl'', ts'')
                                                           (Right _, stbl'', ts'') -> let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                                      in
                                                                                        Left (Error_Excep Excep_assert_failed loc)
                                                           (Left errs, stbl'', ts'') -> Right (Left errs, stbl'', ts'')
                                                        )
                                        return (case r_as' of
                                                  Left err -> Left err
                                                  Right (Right app_args', symtbl'', tokens'') -> Right (Right (Syn_expr_call fun_id app_args' fun_ty), symtbl'', tokens'')
                                                  Right (Left errs, symtbl'', tokens'') -> Right (Left errs, symtbl'', tokens'')
                                               )
                                  _ -> return $ Right (Right (Syn_expr_call fun_id [arg] fun_ty), symtbl', tokens')
                              Right (Nothing, symtbl', tokens') -> return $ Right (Left [], symtbl', tokens')
                         )
                     _ -> let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                          in
                            return $ Right (Left [Internal_error ("Calling the parser for function calling with non function calling parse-tree constructors, in " ++ loc)], symtbl, tokens)
                  )
        case r of
          Left err -> throwE err
          Right r' -> return r'
  in
    let cont_par symtbl subexpr tokens = do
          if par_contp then (
            do
              r <- lift (do
                            r_cont <- runExceptT $ cons_expr symtbl subexpr tokens
                            return (case r_cont of
                                      Left err -> Left err
                                      Right (Right expr', symtbl', tokens') -> Right (Just expr', symtbl', tokens')
                                      Right (Left err, symtbl', tokens') -> Right (Nothing, symtbl', tokens')
                                   )
                        )
              case r of
                Left err -> throwE err
                Right r' -> return r'
            )
            else
            return (Just subexpr, symtbl, tokens)
    in
      case tokens of
        [] -> return (Nothing, symtbl, [])
        Tk_L_par:ts -> do
          r <- lift $ runExceptT $ cons_ptree1 symtbl ts (False, False, True)
          case r of
            Left err -> throwE err
            Right (Just expr, symtbl', (Tk_R_par:ts')) -> cont_par symtbl' (Syn_expr_par expr (syn_node_typeof expr)) ts'
            --Right (Just expr, symtbl', (ts')) -> cont_par symtbl' (Syn_expr_par expr (syn_node_typeof expr)) ts'
            Right (_, symtbl',ts') -> return (Nothing, symtbl', ts')
        
        Tk_if:ts -> do
          r <- lift (do
                        r_cond <- runExceptT $ cons_ptree1 symtbl ts (False, False, True)
                        case r_cond of
                          Left err -> return $ Left err
                          Right (Just cond_expr, symtbl', (Tk_then:ts')) -> do
                            r_true <- runExceptT $ cons_ptree1 symtbl' ts' (False, False, True)
                            case r_true of
                              Left err -> return $ Left err
                              Right (Just true_expr, symtbl'_t, (Tk_else:ts'')) -> do
                                r_false <- runExceptT $ cons_ptree1 symtbl'_t ts'' (False, False, True)
                                case r_false of
                                  Left err -> return $ Left err
                                  Right (Just false_expr, symtbl'', tokens') -> return $ Right (Just (Syn_cond_expr (cond_expr, (true_expr, Just false_expr)) Ty_abs), symtbl'', tokens')
                                  Right (_, symtbl'', tokens') -> return $ Right (Nothing, symtbl'', tokens')
                              Right (Just true_expr, symtbl'', tokens') -> return $ Right (Just (Syn_cond_expr (cond_expr, (true_expr, Nothing)) Ty_abs), symtbl'', tokens')
                              Right (_, symtbl'', tokens') -> return $ Right (Nothing, symtbl'', tokens')
                          Right (_, symtbl', tokens') -> return $ Right (Nothing, symtbl', tokens')
                    )
          case r of
            Left err -> throwE err
            Right r' -> return r'
        
        Tk_decre:ts -> (case ts of
                          (Tk_ident ident):ts' -> cont_par symtbl (Syn_expr_una Ope_decre (Syn_var ident Ty_abs) Ty_abs) ts'
                          _ -> return (Nothing, symtbl, ts)
                       )
        Tk_incre:ts -> (case ts of
                          (Tk_ident ident):ts' -> cont_par symtbl (Syn_expr_una Ope_incre (Syn_var ident Ty_abs) Ty_abs) ts'
                          _ -> return (Nothing, symtbl, ts)
                       )
        Tk_shaft:ts -> (case ts of
                          (Tk_ident ident):ts' -> cont_par symtbl (Syn_expr_una Ope_neg (Syn_var ident Ty_abs) Ty_abs) ts'
                          _ -> return (Nothing, symtbl, ts)
                       )
        
        Tk_false:ts -> cont_par symtbl (Syn_val (Val_bool False) Ty_bool) ts
        Tk_true:ts -> cont_par symtbl (Syn_val (Val_bool True) Ty_bool) ts
        (Tk_nume n):ts -> cont_par symtbl (Syn_val (Val_int n) Ty_int) ts
        (Tk_str s):ts -> cont_par symtbl (Syn_val (Val_str s) Ty_string) ts
        
        Tk_fun:ts -> do
          if fun_declp then
            case ts of
              (Tk_ident fun_id):ts' -> do
                r <- lift (do
                              let fun = Syn_fun_decl' fun_id [] (Syn_scope ([], Syn_none)) (Ty_env [], Ty_abs)
                              r_fun <- runExceptT $ cons_fun_tree'1 symtbl fun ts'
                              case r_fun of
                                Left err -> return $ Left err
                                Right ((fun'@(Syn_fun_decl' fun_id' args' fun_body' (env', fun_ty')), symtbl', tokens'), errs) -> return $ Right (Just fun', symtbl', tokens')
                                Right ((_, symtbl', tokens'), errs) -> let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                       in
                                                                         return $ Left (Error_Excep Excep_assert_failed loc)
                          )
                case r of
                  Left err -> throwE err
                  Right r' -> return r'
              
              _ -> return (Nothing, symtbl, ts)
            else return (Nothing, symtbl, ts)
        
        Tk_var:ts -> if var_declp then
                       do
                         r <- lift (case ts of
                                      (Tk_ident ident):ts' -> do
                                        let var = Syn_var ident Ty_abs
                                        r_v <- runExceptT $ cons_var_decl1 symtbl var ts'
                                        case r_v of
                                          Left err -> return $ Left err
                                          Right ((Just (var_decl@(Syn_var_decl var_id var_ty)), symtbl', tokens'), errs) -> do
                                            let (symtbl'', err_symreg) = sym_regist False symtbl' Sym_cat_decl (var_id, var_decl)
                                            let errs' = errs ++ (case err_symreg of
                                                                   Just e_reg  -> [e_reg]
                                                                   Nothing -> []
                                                                )
                                            return $ Right  (Just var_decl, symtbl'', tokens')
                                          Right ((_, symtbl', tokens'), errs) -> return $ Right (Nothing, symtbl', tokens')
                                      
                                      _ -> return $ Right (Nothing, symtbl, ts)
                                   )
                         case r of
                           Left err ->throwE err
                           Right r' -> return r'
                     else
                       return (Nothing, symtbl, ts)
        
        (Tk_ident ident):ts -> do
          let var = Syn_var ident Ty_abs
          r <- lift (do
                        case ts of
                          Tk_L_par:ts' -> do
                            let fun_app = Syn_expr_call ident [] Ty_abs
                            r_call <- runExceptT $ par_fun_call symtbl fun_app ts'
                            case r_call of
                              Left err -> return $ Left err
                              Right (Right (fun_app'@(Syn_expr_call fun_id app_args app_ty)), symtbl', tokens') -> do
                                case tokens' of
                                  Tk_R_par:ts'' -> runExceptT $ cont_par symtbl' fun_app' ts''
                                  _ -> return $ Right (Nothing, symtbl', tokens')
                              Right (Left errs, symtbl', tokens') -> return $ Right (Nothing, symtbl', tokens')
                          _ -> runExceptT $ cont_par symtbl var ts
                    )
          case r of
            Left err -> throwE err
            Right r' -> return r'
        
        _ -> return (Nothing, symtbl, tokens)

cons_ptree2 :: Symtbl -> [Tk_code] -> (Bool, Bool, Bool) -> ExceptT Error_Excep IO ((Maybe Syntree_node, Symtbl, [Tk_code]), [Error_codes])
cons_ptree2 symtbl tokens (fun_declp, var_declp, par_contp) =
  let cat_err err expr =
        case expr of
          Left err_exc -> throwE err_exc
          Right ((expr0, symtbl', tokens'), err') -> return $ ((expr0, symtbl', tokens'), (err ++ err'))
      
      is_op t = (t == Tk_decre) || (t == Tk_incre) || (t == Tk_slash) || (t == Tk_star) || (t == Tk_shaft) || (t == Tk_cross) || (t == Tk_asgn)
      -- returns true if ope1 >= ope2, otherwise false.
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
                                        _ -> False
                                     )
                          Ope_div -> (case ope2 of
                                        Ope_add -> True
                                        Ope_sub -> True
                                        Ope_mul -> True
                                        Ope_div -> True
                                        _ -> False
                                     )
      
      cons_expr symtbl subexpr1 tokens = do
        let (ope, tokens') = fetch_ope tokens
        case ope of
          Nothing -> return ((Just subexpr1, symtbl, tokens, []), [])
          Just ope' | ope' == Ope_asgn -> do
                        r <- lift (do
                                      rhs <- runExceptT $ cons_ptree2 symtbl tokens' (False, False, True)
                                      case rhs of
                                        Left err_exc -> return $ Left err_exc
                                        Right ((Just expr_r, symtbl', tokens''), err) -> return $ Right ((Just (Syn_expr_asgn subexpr1 expr_r Ty_abs), symtbl', tokens''), err)
                                        Right (Nothing, symtbl', tokens'', err) -> return $ Right ((Just subexpr1, symtbl', tokens''), err)
                                  )
                        case r of
                          Left err_exc -> throwE err_exc
                          Right r' -> return r'
          Just ope' | is_bin_op ope' -> do
                        r <- lift (do
                                      r2 <- runExceptT $ cons_ptree2 symtbl tokens' (False, False, True)
                                      case r2 of
                                        Left err_exc -> return $ Left err_exc
                                        Right ((Just subexpr2, symtbl', tokens''), err) ->
                                          {- return (case subexpr2 of
                                                    Syn_val _ _ -> Right ((Just (Syn_expr_bin ope' (subexpr1, subexpr2) Ty_abs), symtbl', tokens''), err)
                                                    Syn_var _ _ -> Right ((Just (Syn_expr_bin ope' (subexpr1, subexpr2) Ty_abs), symtbl', tokens''), err)
                                                    Syn_expr_bin bin_ope (expr_21, expr_22) _ ->
                                                      if is_gte_op ope' bin_ope then
                                                        ((Right (Syn_expr_bin bin_ope ((lm_im subexpr1 ope' expr_21), expr_22) Ty_abs), symtbl', tokens''), err)
                                                      else
                                                        ((Right (Syn_expr_bin ope' (subexpr1, subexpr2) Ty_abs), symtbl', tokens''), err)
                                                    _ -> ((Right (Syn_expr_bin ope' (subexpr1, subexpr2) Ty_abs), symtbl', tokens''), err)
                                                 ) -}
                                          (case combine subexpr1 ope' subexpr2 of
                                             Right expr' -> return $ Right ((Just expr', symtbl', tokens''), err)
                                             Left exc -> return $ Left exc
                                          )
                                        Right ((Nothing, symtbl', tokens''), err) -> return $ Right ((Just subexpr1, symtbl', tokens''), err)
                                  )
                        case r of
                          Left err -> throwE err
                          Right r' -> return r'
          _ -> let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
               in
                 throwE  (Error_Excep Excep_assert_failed loc)
        
        where
          is_bin_op op = (op == Ope_div) || (op == Ope_mul) || (op == Ope_sub) || (op == Ope_add)
          fetch_ope tokens = case tokens of
                               (Tk_slash:ts) -> (Just Ope_div, ts)
                               (Tk_star:ts) -> (Just Ope_mul, ts)
                               (Tk_shaft:ts) -> (Just Ope_sub, ts)
                               (Tk_cross:ts) -> (Just Ope_add, ts)
                               (Tk_asgn:ts) -> (Just Ope_asgn, ts)
                               _ -> (Nothing, tokens)
          combine expr1 op expr2 =
            case expr2 of
              Syn_expr_par _ _ -> Right $ Syn_expr_bin op (expr1, expr2) Ty_abs
              Syn_val _ _ -> Right $ Syn_expr_bin op (expr1, expr2) Ty_abs
              Syn_var _ _ -> Right $ Syn_expr_bin op (expr1, expr2) Ty_abs
              Syn_expr_call _ _ _ -> Right $ Syn_expr_bin op (expr1, expr2) Ty_abs
              Syn_expr_una _ _ _ -> Right $ Syn_expr_bin op (expr1, expr2) Ty_abs
              Syn_expr_bin op2 (expr21, expr22) ty2 ->
                if is_gte op op2 then
                  case combine expr1 op expr21 of
                    Right expr21' -> Right $ Syn_expr_bin op2 (expr21', expr22) Ty_abs
                    Left exc -> Left exc
                else
                  Right $ Syn_expr_bin op (expr1, expr2) Ty_abs
              _ -> let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                   in
                     Left (Error_Excep Excep_assert_failed loc)
          {- lm_im expr_li bin_ope expr0 = -- means "Left-Most_Inner-Most".
            case expr0 of
              Syn_expr_bin ope_o (expr_o1@(Syn_val _ _), expr_o2) _ | is_gte_op bin_ope ope_o -> Syn_expr_bin ope_o ((Syn_expr_bin bin_ope (expr_li, expr_o1) Ty_abs), expr_o2) Ty_abs
              Syn_expr_bin ope_o (expr_o1@(Syn_var _ _), expr_o2) _ | is_gte_op bin_ope ope_o -> Syn_expr_bin ope_o ((Syn_expr_bin bin_ope (expr_li, expr_o1) Ty_abs), expr_o2) Ty_abs
              Syn_expr_bin ope_o (expr_o1@(Syn_expr_bin ope_o1 _ _), expr_o2) _ | is_gte_op bin_ope ope_o -> Syn_expr_bin ope_o (lm_im expr_li bin_ope expr_o1, expr_o2) Ty_abs
              _ -> Syn_expr_bin bin_ope (expr_li, expr0) Ty_abs -- including Syn_expr_una and Sym_expr_par -}
      
      par_fun_call symtbl fun_app tokens = do
        r <- lift (case fun_app of
                     Syn_expr_call fun_id app_args fun_ty -> do
                       (case tokens of
                          [] -> return $ Right (Right fun_app, symtbl, [])
                          Tk_R_par:ts -> return $ Right (Right fun_app, symtbl, tokens)
                          _ -> do
                            r_a <- runExceptT $ cons_ptree2 symtbl tokens (False, False, False)
                            case r_a of
                              Left err -> return $ Left err
                              Right (Just expr, symtbl', tokens') -> do
                                let arg = case expr of
                                            Syn_var v_id ty -> expr
                                            Syn_expr_call f_id f_args ty -> expr
                                            _ -> expr
                                case tokens' of
                                  Tk_comma:ts' -> do
                                    r_as <- runExceptT $ par_fun_call symtbl' (Syn_expr_call fun_id [] fun_ty) ts'
                                    case r_as of
                                      Left err -> return r_as
                                      Right as' -> do
                                        r_as' <- return (case as' of
                                                           (Right (Syn_expr_call _ args' _), stbl'', ts'') -> Right (Right (arg:args'), stbl'', ts'')
                                                           (Right _, stbl'', ts'') -> let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                                      in
                                                                                        Left (Error_Excep Excep_assert_failed loc)
                                                           (Left errs, stbl'', ts'') -> Right (Left errs, stbl'', ts'')
                                                        )
                                        return (case r_as' of
                                                  Left err -> Left err
                                                  Right (Right app_args', symtbl'', tokens'') -> Right (Right (Syn_expr_call fun_id app_args' fun_ty), symtbl'', tokens'')
                                                  Right (Left errs, symtbl'', tokens'') -> Right (Left errs, symtbl'', tokens'')
                                               )
                                  _ -> return $ Right (Right (Syn_expr_call fun_id [arg] fun_ty), symtbl', tokens')
                              Right (Nothing, symtbl', tokens') -> return $ Right (Left [], symtbl', tokens')
                         )
                     _ -> let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                          in
                            return $ Right (Left [Internal_error ("Calling the parser for function calling with non function calling parse-tree constructors, in " ++ loc)], symtbl, tokens)
                  )
        case r of
          Left err -> throwE err
          Right r' -> return r'
  in
    let cont_par symtbl subexpr tokens = do
          if par_contp then (
            do
              r <- lift (do
                            r_cont <- runExceptT $ cons_expr symtbl subexpr tokens
                            return (case r_cont of
                                      Left err -> Left err
                                      Right ((Just expr', symtbl', tokens'), err) -> Right ((Just expr', symtbl', tokens'), err)
                                      Right ((Nothing, symtbl', tokens'), err) -> Right ((Nothing, symtbl', tokens'), err)
                                   )
                        )
              case r of
                Left err -> throwE err
                Right r' -> return r'
            )
            else
            return ((Just subexpr, symtbl, tokens), [])
    in
      case tokens of
        [] -> return ((Nothing, symtbl, []), [])
        Tk_L_par:ts -> do
          r <- lift $ runExceptT $ cons_ptree2 symtbl ts (False, False, True)
          case r of
            Left err -> throwE err
            Right ((Just par_expr, symtbl', (Tk_R_par:ts')), err) -> do
              r_par <- runExceptT $ cont_par symtbl' (Syn_expr_par par_expr (syn_node_typeof par_expr)) ts'
              case r_par of
                Left err_exc -> throwE err_exc
                Right (r_cont, err_cont) -> return (r_cont, (err ++ err_cont))
            Right ((Just par_expr, symtbl', ts'), err) -> do
              r_par <- (do
                           r_cont <- runExceptT $ cont_par symtbl' (Syn_expr_par par_expr (syn_node_typeof par_expr)) ts'
                           return (case r_cont of
                                     Left err_exc -> Left err_exc
                                     Right ((Just par_expr', symtbl'', ts''), err_cont) -> Right ((Just par_expr', symtbl'', ts''), err')
                                       where
                                         err' = err ++ [Ill_formed_expression errmsg] ++ err_cont
                                     Right ((_, symtbl'', ts''), _) -> Right ((Nothing, symtbl', ts'), err')
                                       where
                                         err' = err ++ [Ill_formed_expression errmsg]
                                  )
                             where
                               errmsg = "Missing R-paren of the expression."
                       )
              case r_par of
                Left err_exc -:> throwE err_exc
                Right r_par' -> return r_par'
            Right ((_, symtbl',ts'), err) -> return ((Nothing, symtbl', ts'), err)
        
        Tk_if:ts -> do
          r <- lift (do
                        r_cond <- runExceptT $ cons_ptree2 symtbl ts (False, False, True)
                        case r_cond of
                          Left err_exc -> return $ Left err_exc
                          Right ((Just cond_expr, symtbl', tokens'), err_c) ->
                            case tokens' of
                              Tk_then:ts' -> do
                                r_true <- runExceptT $ cat_err err_c $ cons_ptree2 symtbl' ts' (False, False, True)
                                case r_true of
                                  Left err_exc -> return $ Left err_exc
                                  Right ((Just true_expr, symtbl'', (Tk_else:ts'')), err_ct) -> return $ par_else_clause err_ct symtbl'' ts''
                                  Right ((Just true_expr, symtbl'', tokens'), err_ct) ->
                                    return $ Right ((Just (Syn_cond_expr (cond_expr, (true_expr, Nothing)) Ty_abs), symtbl'', tokens'), err_ct)
                                  Right ((_, symtbl'', tokens'), err) -> return $ Right ((Nothing, symtbl'', tokens'), err)
                              _ -> return $ Right ((Nothing, symtbl', tokens'), err')
                                where
                                  errmsg = "Expected \"then\", in conditional expression."
                                  err' = err_c ++ [Parse_error errmsg]
                          Right ((_, symtbl', tokens'), err) -> return $ Right ((Nothing, symtbl', tokens'), err)
                          
                          where
                            par_else_clause err symtbl tokens = do
                              r_false <- runExceptT $ cat_err err $ cons_ptree2 symtbl tokens (False, False, True)
                              return (case r_false of
                                        Left err_exc -> Left err_exc
                                        Right ((Just false_expr, symtbl', tokens'), err') ->
                                          Right ((Just (Syn_cond_expr (cond_expr, (true_expr, Just false_expr)) Ty_abs), symtbl', tokens'), err')
                                        Right ((_, symtbl'', tokens'), err') -> Right ((Nothing, symtbl'', tokens'), err')
                                     )
                    )
          case r of
            Left err -> throwE err
            Right r' -> return r'
        
        Tk_decre:ts -> (case ts of
                          (Tk_ident ident):ts' -> cont_par symtbl (Syn_expr_una Ope_decre (Syn_var ident Ty_abs) Ty_abs) ts'
                          _ -> return ((Nothing, symtbl, ts), err)
                            where
                              errmsg = "Expression must be assignable."
                              err = [Ill_formed_expression errmsg]
                       )
        Tk_incre:ts -> (case ts of
                          (Tk_ident ident):ts' -> cont_par symtbl (Syn_expr_una Ope_incre (Syn_var ident Ty_abs) Ty_abs) ts'
                          _ -> return ((Nothing, symtbl, ts), err)
                            where
                              errmsg = "Expression must be assignable."
                              err = [Ill_formed_expression errmsg]
                       )
        Tk_shaft:ts -> do
          r <- lift (do
                        r0 <- runExceptT $ cons_ptree2 symtbl ts (False, False, False)
                        case r0 of
                          Left err -> return $ Left err
                          Right ((Nothing, symtbl', ts'), err) -> return r0
                          Right ((Just expr0, symtbl', ts'), err)-> return $ cat_err err $ cont_par symtbl' (Syn_expr_una Ope_neg expr0 Ty_abs) ts'
                    )
          case r of
            Left err -> throwE err
            Right r' -> return r'
        
        Tk_false:ts -> cont_par symtbl (Syn_val (Val_bool False) Ty_bool) ts
        Tk_true:ts -> cont_par symtbl (Syn_val (Val_bool True) Ty_bool) ts
        (Tk_nume n):ts -> cont_par symtbl (Syn_val (Val_int n) Ty_int) ts
        (Tk_str s):ts -> cont_par symtbl (Syn_val (Val_str s) Ty_string) ts
        
        Tk_fun:ts -> do
          if fun_declp then
            case ts of
              (Tk_ident fun_id):ts' -> do
                r <- lift (do
                              let fun = Syn_fun_decl' fun_id [] (Syn_scope ([], Syn_none)) (Ty_env [], Ty_abs)
                              r_fdecl <- runExceptT $ cons_fun_tree'1 symtbl fun ts'
                              case r_fdecl of
                                Left err -> return $ Left err
                                Right ((fun'@(Syn_fun_decl' fun_id' args' fun_body' (env', fun_ty')), symtbl', tokens'), errs) -> return $ Right ((Just fun', symtbl', tokens'), errs)
                                Right ((_, symtbl', tokens'), errs) -> let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                       in
                                                                         return $ Left (Error_Excep Excep_assert_failed loc)
                          )
                case r of
                  Left err -> throwE err
                  Right r' -> return r'
              
              _ -> return ((Nothing, symtbl, ts), err)
                where
                  errmg = "Invalid function declaration."
                  err = Imcomplete_function_declaration errmsg
            
            else let errmsg = "Illegal function declaration."
                     err = Parse_error errmsg
                 in
                   return ((Nothing, symtbl, ts), err)
            
        Tk_var:ts -> if var_declp then
                       do
                         r <- lift (case ts of
                                      (Tk_ident ident):ts' -> do
                                        let var = Syn_var ident Ty_abs
                                        r_v <- runExceptT $ cons_var_decl1 symtbl var ts'
                                        case r_v of
                                          Left err -> return $ Left err
                                          Right ((Just (var_decl@(Syn_var_decl var_id var_ty)), symtbl', tokens'), errs) -> do
                                            let (symtbl'', err_symreg) = sym_regist False symtbl' Sym_cat_decl (var_id, var_decl)
                                            let errs' = errs ++ (case err_symreg of
                                                                   Just e_reg  -> [e_reg]
                                                                   Nothing -> []
                                                                )
                                            return $ Right ((Just var_decl, symtbl'', tokens'), errs')
                                          Right ((_, symtbl', tokens'), errs) -> return $ Right ((Nothing, symtbl', tokens'), errs)
                                      
                                      _ -> return $ Right ((Nothing, symtbl, ts), err)
                                        where
                                          errmsg = "Invalid variable declaration."
                                          err = Imcomplete_variable_declaration errmsg
                                   )
                         case r of
                           Left err ->throwE err
                           Right r' -> return r'
                     else let errmsg = "Illegal variable declaration."
                              err = Parse_error errmsg
                          in
                            return ((Nothing, symtbl, ts), err)
        
        (Tk_ident ident):ts -> do
          let var = Syn_var ident Ty_abs
          r <- lift (do
                        case ts of
                          Tk_L_par:ts' -> do
                            let fun_app = Syn_expr_call ident [] Ty_abs
                            r_call <- runExceptT $ par_fun_call symtbl fun_app ts'
                            case r_call of
                              Left err -> return $ Left err
                              Right ((Right (fun_app'@(Syn_expr_call fun_id app_args app_ty)), symtbl', tokens'), err) -> do
                                case tokens' of
                                  Tk_R_par:ts'' -> runExceptT $ cat_err err $ cont_par symtbl' fun_app' ts''
                                  _ -> return $ Right ((Nothing, symtbl', tokens'), err)
                                    where
                                      errmg = "Missing closing R paren in function calling."
                                      err = Imcomplete_function_declaration errmsg
                              Right ((Left errs, symtbl', tokens'), err) -> return $ Right ((Nothing, symtbl', tokens'), err)
                          _ -> runExceptT $ cont_par symtbl var ts
                    )
          case r of
            Left err -> throwE err
            Right r' -> return r'
        
        _ -> return (Nothing, symtbl, tokens) -}


type Fresh_tvar = (Type, Integer)

initial_flesh_tvar :: Fresh_tvar
initial_flesh_tvar = (Ty_var $ "t_" ++ (show 0), 0)

succ_flesh_tvar :: Fresh_tvar -> Fresh_tvar
succ_flesh_tvar prev =
  (Ty_var $ "t_" ++ show (last_id + 1), last_id + 1)
  where
    last_id = (snd prev)

ty_curve :: (Syntree_node, Fresh_tvar) -> ExceptT Error_Excep IO (Syntree_node, Fresh_tvar)
ty_curve (expr, prev_tvar) = do
  case expr of
    Syn_arg_decl arg_id Ty_abs -> return (Syn_arg_decl arg_id (fst tvar_arg), tvar_arg)
      where
        tvar_arg = succ_flesh_tvar prev_tvar
    Syn_var var_id Ty_abs -> return (Syn_var var_id (fst tvar_var), tvar_var)
      where
        tvar_var = succ_flesh_tvar prev_tvar
    
    Syn_expr_par expr' ty_par -> do
      r <- lift (do
                    r' <- runExceptT $ ty_curve (expr', prev_tvar)
                    return $ case r' of
                               Left err -> r'
                               Right (expr'', prev_tvar') -> Right (case ty_par of
                                                                      Ty_abs -> (Syn_expr_par expr'' (syn_retrieve_typeof expr''), prev_tvar')
                                                                      _ -> (Syn_expr_par expr'' ty_par, prev_tvar')
                                                                   )
                )
      case r of
        Left err -> throwE err
        Right r' -> return r'
    
    Syn_expr_una ope_una expr' ty_una -> do
      r <- lift (do
                    r' <- runExceptT $ ty_curve (expr', prev_tvar)
                    return $ case r' of
                      Left err -> r'
                      Right (expr'', prev_tvar') -> Right (case ty_una of
                                                             Ty_abs -> (Syn_expr_una ope_una expr'' (fst tvar_una), tvar_una)
                                                               where
                                                                 tvar_una = succ_flesh_tvar prev_tvar'
                                                             _ -> (Syn_expr_una ope_una expr'' ty_una, prev_tvar')
                                                          )
                )
      case r of
        Left err -> throwE err
        Right r' -> return r'
    
    Syn_expr_bin ope_bin (expr1, expr2) ty_bin -> do
      r <- lift (do
                    r1 <- runExceptT $ ty_curve (expr1, prev_tvar)
                    case r1 of
                      Left err -> return r1
                      Right (expr1', prev_tvar') -> do
                        r2 <- runExceptT $ ty_curve (expr2, prev_tvar')
                        return $ case r2 of
                                   Left err -> r2
                                   Right (expr2', prev_tvar'') -> Right (case ty_bin of
                                                                           Ty_abs -> (Syn_expr_bin ope_bin (expr1', expr2') (fst tvar_bin), tvar_bin)
                                                                             where
                                                                               tvar_bin = succ_flesh_tvar prev_tvar''
                                                                           _ -> (Syn_expr_bin ope_bin (expr1', expr2') ty_bin, prev_tvar'')
                                                                        )
                )
      case r of
        Left err -> throwE err
        Right r' -> return r'
    
    Syn_expr_call fun_id args ty_call -> do
      r <- lift (do
                    r_args <- case args of
                                [] -> return $ Right ([], prev_tvar)
                                _ -> runExceptT $ curve_args args prev_tvar
                    return r_args
                )
      case r of
        Left err -> throwE err
        Right (args', prev_tvar') -> return (case ty_call of
                                               Ty_abs -> (Syn_expr_call fun_id args' (fst tvar_call), tvar_call)
                                                 where
                                                   tvar_call = succ_flesh_tvar prev_tvar'
                                               _ -> (Syn_expr_call fun_id args' ty_call, prev_tvar')
                                            )
        where
          curve_args = curve_decls
    
    Syn_cond_expr (cond_expr, (expr_true, expr_false)) ty_cond -> do
      r <- lift (do
                    r_cond <- runExceptT $ ty_curve (cond_expr, prev_tvar)
                    case r_cond of
                      Left err -> return r_cond
                      Right (cond_expr', prev_tvar') -> do
                        r_true <- runExceptT $ ty_curve (expr_true, prev_tvar')
                        case r_true of
                          Left err -> return r_true
                          Right (expr_true', prev_tvar'') -> do
                            r_false <- (case expr_false of
                                          Nothing -> return $ Right (Nothing, prev_tvar'')
                                          Just f_expr_body -> do
                                            r_false' <- runExceptT $ ty_curve (f_expr_body, prev_tvar'')
                                            case r_false' of
                                              Left err -> return $ Left err
                                              Right (f_expr_body', latest) -> return $ Right (Just f_expr_body', latest)
                                       )
                            case r_false of
                              Left err -> return $ Left err
                              Right (expr_false', latest') -> return $ Right (case ty_cond of
                                                                                Ty_abs -> (Syn_cond_expr (cond_expr', (expr_true', expr_false')) (fst tvar_cond), tvar_cond)
                                                                                  where
                                                                                    tvar_cond = succ_flesh_tvar latest'
                                                                                _ -> (Syn_cond_expr (cond_expr', (expr_true', expr_false')) ty_cond, latest')
                                                                             )
                )
      case r of
        Left err -> throwE err
        Right r' -> return r'
    
    Syn_fun_decl' fun_id args fun_body (_, ty_fun) -> do
      r <- lift $ (do
                      r_args <- case args of
                                  [] -> return $ Right ([], prev_tvar)
                                  _ -> runExceptT $ curve_decls args prev_tvar
                      case r_args of
                        Left err -> return $ Left err
                        Right (args', prev_tvar') -> do
                          r_body <- runExceptT $ ty_curve (fun_body, prev_tvar')
                          case r_body of
                            Left err -> return r_body
                            Right (fun_body', prev_tvar'') -> return $ Right (Syn_fun_decl fun_id args' fun_body' ty_fun', latest)
                              where
                                (ty_fun', latest) = case ty_fun of
                                                      Ty_abs -> curve_funty (args', ty_fun) prev_tvar''
                                                      _ -> (ty_fun, prev_tvar'')
                                curve_funty :: ([Syntree_node], Type) -> Fresh_tvar -> (Type, Fresh_tvar)
                                curve_funty (args, fun_ty) prev_tvar =
                                  let from_args = Prelude.foldl (\(as', prev_tv) -> (\a -> case syn_node_typeof a of
                                                                                             Ty_abs -> (as' ++ [fst prev_tv'], prev_tv')
                                                                                               where
                                                                                                 prev_tv' = succ_flesh_tvar prev_tv
                                                                                             (a_ty@_) -> (as' ++ [a_ty], prev_tv)
                                                                                    )
                                                                ) ([], prev_tvar) args
                                  in
                                    case from_args of
                                      (args', prev_tvar') -> (case fun_ty of
                                                                Ty_abs -> (Ty_fun args' (fst tvar_fun_decl), tvar_fun_decl)
                                                                  where
                                                                    tvar_fun_decl = succ_flesh_tvar prev_tvar'
                                                                _ -> (Ty_fun args' fun_ty, prev_tvar')
                                                             )
                  )
      case r of
        Left err -> throwE err
        Right r' -> return r'
    
    Syn_var_decl var_id Ty_abs -> return (Syn_var_decl var_id (fst tvar_var), tvar_var)
      where
        tvar_var = succ_flesh_tvar prev_tvar
    
    Syn_expr_seq exprs seq_ty -> do
      r <- lift (do
                    r_exprs <- case exprs of
                                 [] -> return $ Right ([], prev_tvar)
                                 e:es -> do
                                   r_e <- runExceptT $ ty_curve (e, prev_tvar)
                                   case r_e of
                                     Left err -> return $ Left err
                                     Right (e', prev_tvar') -> (do
                                                                   r_es <- runExceptT $ curve_seqs es prev_tvar'
                                                                   case r_es of
                                                                     Left err -> return r_es
                                                                     Right (es', prev_tvar'') -> return $ Right ((e':es'), prev_tvar'')
                                                               )
                                       where
                                         curve_seqs = curve_decls
                    case r_exprs of
                      Left err -> return $ Left err
                      Right (exprs', latest) -> return $ Right (case seq_ty of
                                                                  Ty_abs -> (Syn_expr_seq exprs' (syn_retrieve_typeof seq_expr_raw), latest)
                                                                    where
                                                                      seq_expr_raw = Syn_expr_seq exprs' seq_ty
                                                                  _ -> (Syn_expr_seq exprs' seq_ty, latest)
                                                               )
                )
      case r of
        Left err -> throwE err
        Right r'-> return r'
    
    Syn_scope (decls, body) -> do
      r <- lift (do
                    r_decls <- runExceptT $ curve_decls decls prev_tvar
                    case r_decls of
                      Left err -> return $ Left err
                      Right (decls', prev_tvar') -> do
                        r_body <- runExceptT $ ty_curve (body, prev_tvar')
                        case r_body of
                          Left err -> return r_body
                          Right (body', latest) -> return $ Right (Syn_scope (decls', body'), latest)
                )
      case r of
        Left err -> throwE err
        Right r' -> return r'
    
    Syn_expr_asgn expr_l expr_r ty_asgn -> do
      r <- lift (do
                    r_l <- runExceptT $ ty_curve (expr_l, prev_tvar)
                    case r_l of
                      Left err -> return r_l
                      Right (expr_l', prev_tvar') -> do
                        r_r <- runExceptT $ ty_curve (expr_r, prev_tvar')
                        case r_r of
                          Left err -> return r_r
                          Right (expr_r', prev_tvar'') -> return $ Right (Syn_expr_asgn expr_l' expr_r' ty_asgn', prev_tvar'')
                          where
                            ty_asgn' = case ty_asgn of
                                         Ty_abs -> syn_retrieve_typeof expr_l'
                                         _ -> ty_asgn
                )
      case r of
        Left err -> throwE err
        Right r' -> return r'

    Syn_val _ Ty_abs -> let loc  = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                        in
                          throwE (Error_Excep Excep_assert_failed loc)
    
    _ -> return (expr, prev_tvar) -- including the case of  Syn_tydef_decl, Syn_rec_decl, and Syn_none.
  
  where
    curve_decls :: [Syntree_node] -> Fresh_tvar -> ExceptT Error_Excep IO ([Syntree_node], Fresh_tvar)
    curve_decls decls prev_tvar = do
      r <- lift (do
                    case decls of
                      [] -> return $ Right ([], prev_tvar)
                      a:as -> do
                        r' <- runExceptT $ ty_curve (a, prev_tvar)
                        case r' of
                          Left err -> return (Left err)
                          Right (a', prev_tvar') -> do
                            r'' <- runExceptT $ curve_decls as prev_tvar'
                            return $ case r'' of
                                       Left err -> r''
                                       Right (as', prev_tvar'') -> Right (a':as', prev_tvar'')
                )
      case r of
        Left err -> throwE err
        Right r' -> return r'


type Equation = (Type, Type)

ty_unif :: [Equation] -> Maybe [Subst]
ty_unif equs =
  case equs of
    [] -> Just []
    _ -> (case rewrite equs [] of
            Just ([], substs) -> Just substs
            _ -> Nothing
         )
      where
        rewrite :: [Equation] -> [Subst] -> Maybe ([Equation], [Subst])
        rewrite equs substs =
          case equs of
            [] -> Just ([], substs)
            (e_lhs, e_rhs):es | e_lhs == e_rhs -> rewrite es substs
            (tv@(Ty_var tvar_id), e_rhs):es | not $ Set.member tvar_id (Set.fromList (ty_ftv e_rhs)) -> let s = (tvar_id, e_rhs)
                                                                                                            equs' = Prelude.map (\(lhs, rhs) -> ((ty_subst [s] lhs), (ty_subst [s] rhs))) es
                                                                                                            substs' = Prelude.map (\(tv_id, ty_mapsto) -> (tv_id, (ty_subst [s] ty_mapsto))) substs
                                                                                                        in
                                                                                                          rewrite equs' (substs ++ [s])
            (e_lhs, tv@(Ty_var tvar_id)):es | not $ Set.member tvar_id (Set.fromList (ty_ftv e_lhs)) -> let s = (tvar_id, e_lhs)
                                                                                                            equs' = Prelude.map (\(lhs, rhs) -> ((ty_subst [s] lhs), (ty_subst [s] rhs))) es
                                                                                                            substs' = Prelude.map (\(tv_id, ty_mapsto) -> (tv_id, (ty_subst [s] ty_mapsto))) substs
                                                                                                        in
                                                                                                          rewrite equs' (substs ++ [s])
            (Ty_pair(e1_lhs, e1_rhs), rhs):es -> (case rhs of
                                                    Ty_pair (e2_lhs, e2_rhs) -> rewrite ((e1_lhs, e2_lhs):(e1_rhs, e2_rhs):es) substs
                                                    _ -> Nothing
                                                 )
            _ -> Nothing


ty_overlap_env :: Ty_env -> Ty_env -> [Equation]
ty_overlap_env env1 env2 =
  case env1 of
    Ty_env [] -> []
    Ty_env es1 -> case env2 of
                    Ty_env [] -> []
                    Ty_env es2 -> let overlaps = Set.intersection (Set.fromList $ Prelude.map fst es1) (Set.fromList $ Prelude.map fst es2)
                                  in
                                    if Set.null overlaps then [] else case Set.toList overlaps of                                      
                                                                        [] -> []
                                                                        vs -> pairing vs
                                                                          where
                                                                            pairing [] = []
                                                                            pairing (v:vs) =
                                                                              case (Prelude.lookup v es1, Prelude.lookup v es2) of
                                                                                (Just ty1_mapsto, Just ty2_mapsto) -> (ty1_mapsto, ty2_mapsto):(pairing vs)
                                                                                _ -> pairing vs
ty_overlap_env1 :: Ty_env -> Ty_env -> ((Ty_env, Ty_env), [Equation])
ty_overlap_env1 env1 env2 =
  case env1 of
    Ty_env [] -> ((env1, env2), [])
    Ty_env es1 -> case env2 of
                    Ty_env [] -> ((env1, env2), [])
                    Ty_env es2 -> let overlaps = Set.intersection (Set.fromList $ Prelude.map fst es1) (Set.fromList $ Prelude.map fst es2)
                                  in
                                    case Set.toList overlaps of
                                      [] -> ((env1, env2), [])
                                      vs -> (case enum_equs vs (es1, es2) of
                                               ((es1', es2'), equs) -> ((Ty_env es1', Ty_env es2'), equs)
                                            )
                                        where
                                          enum_equs :: [String] -> ([(String, Type)], [(String, Type)]) -> (([(String, Type)], [(String, Type)]), [Equation])
                                          enum_equs overlaps (es1, es2) =
                                            case overlaps of
                                              [] -> ((es1, es2), [])
                                              (v:vs) -> (case (Prelude.lookup v es1, Prelude.lookup v es2) of
                                                           (Just ty_es1, Just ty_es2) -> (case ty_lcs ty_es1 ty_es2 of
                                                                                            Just lcs -> go_on v (ty_es1, ty_es2, lcs)
                                                                                            Nothing -> (case ty_lcs ty_es2 ty_es1 of
                                                                                                          Just lcs' -> go_on v (ty_es1, ty_es2, lcs')
                                                                                                          Nothing -> (case enum_equs vs (es1, es2) of
                                                                                                                        ((es1', es2'), equs) -> ((es1', es2'), (ty_es1, ty_es2):equs)
                                                                                                                     )
                                                                                                       )
                                                                                         )
                                                             where
                                                               go_on :: String -> (Type, Type, Type) -> (([(String, Type)], [(String, Type)]), [Equation])
                                                               go_on var_id (ty1_mapsto, ty2_mapsto, ty_lcs) =
                                                                 let s_es1' = Set.toList $ Set.difference (Set.fromList es1) (Set.fromList [(var_id, ty1_mapsto)])
                                                                     s_es2' = Set.toList $ Set.difference (Set.fromList es2) (Set.fromList [(var_id, ty2_mapsto)])
                                                                 in
                                                                   enum_equs vs ((s_es1' ++ [(var_id, ty_lcs)]), (s_es2' ++ [(var_id, ty_lcs)]))
                                                           _ -> enum_equs vs (es1, es2)
                                                        )


ty_cat_env :: Ty_env -> Ty_env -> Ty_env
ty_cat_env env1 env2 =
  case env1 of
    Ty_env [] -> env2
    Ty_env env1' -> (case env2 of
                       Ty_env [] -> env1
                       Ty_env env2' -> Ty_env $ concat [env1', env2']
                    )

ty_ovwt_env :: Ty_env -> Ty_env -> Ty_env
ty_ovwt_env env_1 env_2 =
  case env_1 of
    Ty_env [] -> env_2
    Ty_env es1 -> case env_2 of
                    Ty_env [] -> env_1
                    Ty_env es2 -> Ty_env $ Prelude.foldl (\env1 -> \(var, ty) -> case Prelude.lookup var env1 of
                                                                                   Just ty' -> let s_env1 = Set.fromList env1
                                                                                                   s_bind = Set.fromList [(var, ty')]
                                                                                               in
                                                                                                 (Set.toList (Set.difference s_env1 s_bind)) ++ [(var, ty)]
                                                                                   Nothing -> env1 ++ [(var, ty)]
                                                         ) es1 es2

ty_merge_env :: Ty_env -> Ty_env -> Maybe Ty_env
ty_merge_env env_1 env_2 =
  case env_2 of
    Ty_env [] -> Just env_1
    Ty_env bs_2 -> (case env_1 of
                      Ty_env [] -> Just  env_2
                      Ty_env bs_1 -> (case chk_and_merge bs_1 bs_2 of
                                        Just bs_m -> Just (Ty_env bs_m)
                                        Nothing -> Nothing
                                     )
                   )
      where
        chk_and_merge env1_binds env2_binds = Prelude.foldl (\e1_bs -> \(id, ty) -> do
                                                                e1_bs' <- e1_bs
                                                                e1_bs'' <- (case Prelude.lookup id e1_bs' of
                                                                               Nothing -> Just e1_bs'
                                                                               Just ty_e1 | ty_e1 == ty -> Just e1_bs'
                                                                               _ -> Nothing
                                                                           )
                                                                return $ e1_bs'' ++ [(id, ty)]
                                                            ) (Just env1_binds) env2_binds
        


ty_inf_expr :: Symtbl -> Syntree_node -> ExceptT ((Ty_env, Syntree_node), Symtbl, [Error_codes]) IO ((Ty_env, Syntree_node), Symtbl, [Error_codes])
ty_inf_expr symtbl expr =
  case expr of
    Syn_val (Val_bool b) ty_b -> if ty_b == Ty_bool then return ((Ty_env [], expr), symtbl, [])
                                 else throwE ((Ty_env [], expr), symtbl, [Illtyped_constant])
    Syn_val (Val_int n) ty_n -> if (ty_n == Ty_int) then return ((Ty_env [], expr), symtbl, [])
                                else throwE ((Ty_env [], expr), symtbl, [Illtyped_constant])
    Syn_val (Val_str s) ty_s -> if (ty_s == Ty_string) then return ((Ty_env [], expr), symtbl, [])
                                else throwE ((Ty_env [], expr), symtbl, [Illtyped_constant])
    Syn_var v_id v_ty -> case sym_lkup_var_decl symtbl v_id of
                           Just (Sym_attrib { sym_attr_entity = v_attr }, symtbl') ->
                             (case v_attr of
                                 Syn_var v_id' v_ty_decl | v_id == v_id' -> (case ty_lcs v_ty v_ty_decl of
                                                                               Just lcs -> return ((Ty_env [(v_id, v_ty)], expr), symtbl', [])
                                                                               Nothing -> let equ = (v_ty, v_ty_decl)
                                                                                          in
                                                                                            case ty_unif [equ] of
                                                                                              Just u_var -> let env' = Ty_env [(v_id, (ty_subst u_var v_ty))]
                                                                                                                expr' = Syn_var v_id (ty_subst u_var v_ty)
                                                                                                            in
                                                                                                              return ((env', expr'), symtbl', [])
                                                                                              Nothing -> throwE ((Ty_env [(v_id, v_ty)], expr), symtbl', [Type_constraint_mismatched errmsg])
                                                                                                where
                                                                                                  errmsg = "type of " ++ v_id ++ " does'nt meet with its declaration."
                                                                            )
                                 _ -> throwE ((Ty_env [(v_id, v_ty)], expr), symtbl', [Internal_error errmsg])
                                   where
                                     errmsg = "ill-registration detected in symbol table, for " ++ v_id
                             )
                           Nothing -> let (symtbl', reg_err) = sym_regist False symtbl Sym_cat_decl (v_id, expr)
                                      in
                                        case reg_err of
                                          Nothing -> return ((Ty_env [(v_id, v_ty)], expr), symtbl', [])
                                          Just err -> throwE ((Ty_env [(v_id, v_ty)], expr), symtbl', [Internal_error errmsg])
                                            where
                                              errmsg = "failed to regist on symbol table, for " ++ v_id
    
    Syn_expr_asgn expr_l expr_r ty -> do
      ((env_l, expr_l_inf), symtbl_l, err_l) <- ty_inf symtbl expr_l
      case expr_l_inf of
        Syn_var var_id var_ty -> do
          ((env_r, expr_r_inf), symtbl_r, err_r) <- ty_inf symtbl_l expr_r
          let ((env_l', env_r'), equ_env) = ty_overlap_env1 env_l env_r
          let equ_asgn = ((syn_node_typeof expr_l_inf), (syn_node_typeof expr_r_inf))
          case ty_unif (equ_asgn:equ_env) of
            Just u_asgn -> let env_l_inf = ty_subst_env u_asgn env_l'
                               expr_l_inf' = syn_node_subst u_asgn expr_l_inf
                               env_r_inf = ty_subst_env u_asgn env_r'
                               expr_r_inf' = syn_node_subst u_asgn expr_r_inf
                           in
                             case ty_merge_env env_l_inf env_r_inf of
                               Just e_merged -> if (syn_node_typeof expr_l_inf') == (syn_node_typeof expr_r_inf') then
                                                  return ((e_merged, Syn_expr_asgn expr_l_inf' expr_r_inf' (syn_node_typeof expr_l_inf')), symtbl_r, (err_l ++ err_r))
                                                else
                                                  let errmsg = "ill unification detected in type reconstruction on assignment expression."
                                                  in
                                                    throwE ((e_merged, Syn_expr_asgn expr_l_inf' expr_r_inf' (syn_node_typeof expr_l_inf')),
                                                            symtbl_r, (err_l ++ err_r ++ [Internal_error errmsg]))
                               Nothing -> throwE ((ty_ovwt_env env_l_inf env_r_inf, Syn_expr_asgn expr_l_inf' expr_r_inf' (syn_node_typeof expr_l_inf')),
                                                  symtbl_r, (err_l ++ err_r ++ [Internal_error errmsg]))
                                 where
                                   errmsg = "ill unification detected in type reconstruction on assignment expression."
            Nothing -> throwE ((ty_ovwt_env env_l env_r, Syn_expr_asgn expr_l_inf expr_r_inf (syn_node_typeof expr_l_inf)), symtbl_r, (err_l ++ err_r ++ [Internal_error errmsg]))
              where
                errmsg = "both left and right expressions must have same type, in assignment expression."
        _ -> do
          ((env_r, expr_r_inf), symtbl_r, err_r) <- ty_inf symtbl_l expr_r
          throwE ((ty_ovwt_env env_l env_r, Syn_expr_asgn expr_l_inf expr_r_inf (syn_node_typeof expr_l_inf)), symtbl_r, (err_l ++ err_r ++ [Internal_error errmsg]))
          where
            errmsg = "left expression must be lvalue in assignment expression"
    
    Syn_cond_expr (cond_expr, (true_expr, false_expr)) ty -> do
      ((env_cond, cond_expr_inf), symtbl_c, cond_err) <-
        do
          r_cond' <- lift (do
                              r_cond <- runExceptT $ ty_inf_expr symtbl cond_expr
                              case r_cond of
                                Right r -> return r_cond
                                Left ((env_c, c_expr_inf), symtbl', c_err) -> return $ Left ((env_c, expr'), symtbl', c_err)
                                  where
                                    expr' = Syn_cond_expr (c_expr_inf, (true_expr, false_expr)) ty
                          )
          case r_cond' of
            Right r' -> return r'
            Left r' -> throwE r'
      
      ((env_cond', cond_expr_inf'), symtbl_c', cond_err') <- let equ_cond = ((syn_node_typeof cond_expr_inf), Ty_bool)
                                                             in
                                                               case ty_unif [equ_cond] of
                                                                 Just u_expr_c -> return (((ty_subst_env u_expr_c env_cond), (syn_node_subst u_expr_c cond_expr_inf)), symtbl_c, cond_err)
                                                                 Nothing -> throwE ((env_cond, expr'), symtbl_c, (cond_err ++ [Type_constraint_mismatched errmsg]))
                                                                   where
                                                                     expr' = Syn_cond_expr (cond_expr_inf, (true_expr, false_expr)) ty
                                                                     errmsg = "conditional clause of conditional expression must be boolean."
      ((env_true, true_expr_inf), symtbl_ct, true_err) <- do
        r_true' <- lift (do
                            r_true <- runExceptT $ ty_inf_expr symtbl_c' true_expr
                            case r_true of
                              Right r -> return r_true
                              Left ((env_t, t_expr_inf), symtbl', t_err) -> return $ Left ((env', expr'), symtbl', (cond_err' ++ t_err))
                                where
                                  env' = ty_ovwt_env env_cond' env_t
                                  expr' = Syn_cond_expr (cond_expr_inf', (t_expr_inf, false_expr)) (syn_node_typeof t_expr_inf)
                        )
        case r_true' of
          Right r' -> return r'
          Left r' -> throwE r'
      
      ((env'', if_expr_inf), symtbl'', if_expr_err') <-
        let equ_cond = ((syn_node_typeof cond_expr_inf), Ty_bool)
        in
          case false_expr of
            Nothing -> let ((env_cond'', env_true'), equs_cond_true) = ty_overlap_env1 env_cond env_true
                       in
                         case ty_unif (equ_cond:equs_cond_true) of
                           Just u_ct -> let env_cond_inf =  ty_subst_env u_ct env_cond''
                                            cond_expr_inf'' = syn_node_subst u_ct cond_expr_inf
                                            env_true_inf = ty_subst_env u_ct env_true'
                                            true_expr_inf' = syn_node_subst u_ct true_expr_inf
                                        in
                                          case ty_merge_env env_cond_inf env_true_inf of
                                            Just e_merged -> if ((syn_node_typeof cond_expr_inf'') == Ty_bool) then
                                                               return ((e_merged, Syn_cond_expr (cond_expr_inf'', (true_expr_inf', Nothing)) (syn_node_typeof true_expr_inf')),
                                                                       symtbl_ct, (cond_err' ++ true_err))
                                                             else
                                                               let errmsg = "ill unification detected in type reconstruction."
                                                               in
                                                                 throwE ((e_merged, Syn_cond_expr (cond_expr_inf'', (true_expr_inf', Nothing)) (syn_node_typeof true_expr_inf')),
                                                                         symtbl_ct, (cond_err' ++ true_err ++ [Internal_error errmsg]))
                                            Nothing -> throwE (((ty_ovwt_env env_cond_inf env_true_inf), Syn_cond_expr (cond_expr_inf'', (true_expr_inf', Nothing)) (syn_node_typeof true_expr_inf')),
                                                               symtbl_ct, (cond_err' ++ true_err ++ [Internal_error errmsg]))
                                              where
                                                errmsg = "ill unification detected in type environment construction."
                           Nothing -> throwE (((ty_ovwt_env env_cond' env_true), Syn_cond_expr (cond_expr_inf', (true_expr_inf, Nothing)) (syn_node_typeof true_expr_inf)),
                                              symtbl_ct, (cond_err' ++ true_err ++ [Type_constraint_mismatched errmsg]))
                             where
                               errmsg = "type inference on true clause doesn't meet with its conditional expression."
            Just f_expr -> do
              ((env_false, false_expr_inf), symtbl_ctf, false_err) <- ty_inf_expr symtbl_ct f_expr
              let equ_if_body = ((syn_node_typeof true_expr_inf), (syn_node_typeof false_expr_inf))
              let ((env_cond'', env_true'), equs_cond_true) = ty_overlap_env1 env_cond env_true
              let ((env_cond''', env_false'), equs_cond_false) = ty_overlap_env1 env_cond'' env_false
              let ((env_true'', env_false''), equs_true_false) = ty_overlap_env1 env_true' env_false'
              case ty_unif (equ_cond:equ_if_body:(equs_cond_true ++ equs_cond_false ++ equs_true_false)) of
                Just u_ctf -> let env_cond_inf =  ty_subst_env u_ctf env_cond'''
                                  cond_expr_inf'' = syn_node_subst u_ctf cond_expr_inf
                                  env_true_inf = ty_subst_env u_ctf env_true''
                                  true_expr_inf' = syn_node_subst u_ctf true_expr_inf
                                  env_false_inf = ty_subst_env u_ctf env_false''
                                  false_expr_inf' = syn_node_subst u_ctf false_expr_inf
                              in
                                case (do
                                         env_ct <- ty_merge_env env_cond_inf env_true_inf
                                         env_ctf <- ty_merge_env env_ct env_false_inf
                                         return env_ctf
                                     ) of
                                  Just e_merged -> (do
                                                       
                                                       if ((syn_node_typeof cond_expr_inf'') == Ty_bool) && ((syn_node_typeof true_expr_inf') == (syn_node_typeof false_expr_inf')) then 
                                                         do
                                                           return ((e_merged, Syn_cond_expr (cond_expr_inf'', (true_expr_inf', Just false_expr_inf')) (syn_node_typeof true_expr_inf')),
                                                                   symtbl_ct, (cond_err' ++ true_err ++ false_err))
                                                         else
                                                         let errmsg = "ill unification detected in type reconstruction."
                                                         in
                                                           throwE ((e_merged, Syn_cond_expr (cond_expr_inf'', (true_expr_inf', Just false_expr_inf')) (syn_node_typeof true_expr_inf')),
                                                                   symtbl_ct, (cond_err' ++ true_err ++ false_err ++ [Internal_error errmsg]))
                                                   )
                                  Nothing -> throwE (((ty_ovwt_env (ty_ovwt_env env_cond_inf env_true_inf)  env_false_inf),
                                                      Syn_cond_expr (cond_expr_inf', (true_expr_inf', Just false_expr_inf')) (syn_node_typeof true_expr_inf')),
                                                      symtbl_ct, (cond_err' ++ true_err ++ false_err ++ [Internal_error errmsg]))
                                    where
                                      errmsg = "ill unification detected in type environment construction."
                Nothing -> (case ty_unif (equ_if_body:equs_true_false) of
                              Just u_tf -> let env_true_inf = ty_subst_env u_tf env_true''
                                               true_expr_inf' = syn_node_subst u_tf true_expr_inf
                                               env_false_inf = ty_subst_env u_tf env_false''
                                               false_expr_inf' = syn_node_subst u_tf false_expr_inf
                                           in
                                             throwE (((ty_ovwt_env (ty_ovwt_env env_cond' env_true_inf) env_false_inf),
                                                      Syn_cond_expr (cond_expr_inf', (true_expr_inf', Just false_expr_inf')) (syn_node_typeof true_expr_inf')),
                                                      symtbl_ct, (cond_err' ++ true_err ++ false_err ++ [Type_constraint_mismatched errmsg]))
                                where
                                  errmsg = "conditional expression should consist of boolean condition, and same type clauses for both true/false."
                              Nothing -> throwE (((ty_ovwt_env (ty_ovwt_env env_cond' env_true) env_false),
                                                  Syn_cond_expr (cond_expr_inf, (true_expr_inf, Just false_expr_inf)) (syn_node_typeof true_expr_inf)),
                                                  symtbl_ct, (cond_err' ++ true_err ++ false_err ++ [Type_constraint_mismatched errmsg]))
                                where
                                  errmsg = "true/false clauses of conditional expression must have same type."
                         )
      return ((env'', if_expr_inf), symtbl'', if_expr_err')
    
    Syn_expr_call fun_id app_args ty -> return ((Ty_env [], expr), symtbl, [])
    
    Syn_expr_par expr0 ty -> do
      r_expr0' <- lift (do
                           r_expr0 <- runExceptT $ ty_inf symtbl expr0
                           case r_expr0 of
                             Right ((env0, expr0_inf), symtbl', expr0_err) -> return $ Right ((env0, expr'), symtbl', expr0_err)
                               where
                                 expr' = Syn_expr_par expr0_inf (syn_node_typeof expr0_inf)
                             Left ((env0, expr0_inf), symtbl', expr0_err) ->  return $ Left ((env0, expr'), symtbl', expr0_err)
                               where
                                 expr' = Syn_expr_par expr0_inf (syn_node_typeof expr0_inf)
                       )
      case r_expr0' of
        Right r' -> return r'
        Left r' -> throwE r'
    
    Syn_expr_una ope expr0 ty -> do
      ((env, expr0_inf), symtbl', una_err) <- do
        r_expr0' <- lift (do
                             r_expr0 <- runExceptT $ ty_inf_expr symtbl expr0
                             case r_expr0 of
                               Right r -> return r_expr0
                               Left ((env0, e0_inf), symtbl', e0_err) -> return $ Left ((env0, e0_inf'), symtbl', e0_err)
                                 where
                                   e0_inf' = Syn_expr_una ope e0_inf (syn_node_typeof e0_inf)
                         )
        case r_expr0' of
          Right r' -> return r'
          Left r' -> throwE r'
      let expr_una_inf = Syn_expr_una ope expr0_inf (syn_node_typeof expr0_inf)
      return ((env, expr_una_inf), symtbl', una_err)
    
    Syn_expr_bin ope (expr1, expr2) ty -> do
      ((env1, expr1_inf), symtbl_1, err1) <- do
        r_expr1' <- lift (do
                             r_expr1 <- runExceptT $ ty_inf_expr symtbl expr1
                             case r_expr1 of
                               Right r -> return r_expr1
                               Left ((env1', e1_inf), symtbl', e1_err) -> return $ Left ((env1', expr'), symtbl', e1_err)
                                 where
                                   expr' = Syn_expr_bin ope (e1_inf, expr2) (syn_node_typeof e1_inf)
                         )
        case r_expr1' of
          Right r' -> return r'
          Left r' -> throwE r'
      
      ((env2, expr2_inf), symtbl_2, err2) <- do
        r_expr2' <- lift (do
                             r_expr2 <- runExceptT $ ty_inf_expr symtbl_1 expr2
                             case r_expr2 of
                               Right r -> return r_expr2
                               Left ((env2', e2_inf), symtbl', e2_err) -> return $ Left ((env', expr'), symtbl', (err1 ++ e2_err))
                                 where
                                   env' = ty_ovwt_env env1 env2'
                                   expr' = Syn_expr_bin ope (expr1_inf, e2_inf) (syn_node_typeof e2_inf)
                         )
        case r_expr2' of
          Right r' -> return r'
          Left r' -> throwE r'
      
      let ((expr1_inf', expr2_inf'), equ_bin_op) = case ty_lcs (syn_node_typeof expr1_inf) (syn_node_typeof expr2_inf) of
                                                     Just lcs -> ((e1_inf', e2_inf'), [])                                                     
                                                       where
                                                         e1_inf' = syn_node_promote expr1_inf lcs
                                                         e2_inf' = syn_node_promote expr2_inf lcs
                                                     Nothing -> ((expr1_inf, expr2_inf), [equ])
                                                       where
                                                         equ = ((syn_node_typeof expr1_inf), (syn_node_typeof expr2_inf))
      let ((env1', env2'), equ_env') = ty_overlap_env1 env1 env2
      lift $ putStrLn ("equations: " ++ (show equ_bin_op) ++ (show equ_env'))
      ((env'', expr_bin_inf), symtbl', err') <- case ty_unif (equ_bin_op ++ equ_env') of
                                                  Just u_bin -> let ty1_inf' = ty_subst u_bin $ syn_node_typeof expr1_inf'
                                                                    ty2_inf' = ty_subst u_bin $ syn_node_typeof expr2_inf'
                                                                in
                                                                  case ty_lcs ty1_inf' ty2_inf' of
                                                                    Just lcs' -> let expr1_inf'' = syn_node_promote expr1_inf' lcs'
                                                                                     expr2_inf'' = syn_node_promote expr2_inf' lcs'
                                                                                 in
                                                                                   do
                                                                                     case ty_merge_env (ty_subst_env u_bin env1') (ty_subst_env u_bin env2') of
                                                                                       Just env' -> return ((env', (Syn_expr_bin ope (expr1_inf'', expr2_inf'') lcs')), symtbl_2, (err1 ++ err2))
                                                                                       Nothing -> throwE ((env', (Syn_expr_bin ope (expr1_inf'', expr2_inf'') lcs')), symtbl_2,
                                                                                                          (err1 ++ err2) ++ [Internal_error errmsg])
                                                                                         where
                                                                                           env' = ty_ovwt_env (ty_subst_env u_bin env1') (ty_subst_env u_bin env2')
                                                                                           errmsg = "ill unification detected in type reconstruction."
                                                                    Nothing -> let expr1_inf'' = syn_node_promote expr1_inf' ty1_inf'
                                                                                   expr2_inf'' = syn_node_promote expr2_inf' ty2_inf'
                                                                               in
                                                                                 do
                                                                                   throwE ((env2', (Syn_expr_bin ope (expr1_inf'', expr2_inf'') (syn_node_typeof expr2_inf''))), symtbl_2,
                                                                                           (err1 ++ err2) ++ [Type_constraint_mismatched errmsg])
                                                                      where
                                                                        env' = ty_ovwt_env (ty_subst_env u_bin env1') (ty_subst_env u_bin env2')
                                                                        errmsg = "operands lost common type on binary operation of " ++ (show ope)
                                                  Nothing -> let ty1_inf' = syn_node_typeof expr1_inf'
                                                                 ty2_inf' = syn_node_typeof expr2_inf'
                                                             in
                                                               (do 
                                                                   case ty_lcs ty1_inf' ty2_inf' of
                                                                     Just lcs' -> throwE ((env', (Syn_expr_bin ope (expr1_inf', expr2_inf') lcs')), symtbl_2,
                                                                                          (err1 ++ err2) ++ [Type_constraint_mismatched errmsg])
                                                                       where
                                                                         errmsg = "type environments of operands doesn't meet, in binary operation of " ++ (show ope)
                                                                     Nothing -> throwE ((env', (Syn_expr_bin ope (expr1_inf', expr2_inf') (syn_node_typeof expr2_inf'))), symtbl_2,
                                                                                        (err1 ++ err2) ++ [Type_constraint_mismatched errmsg])
                                                                       where
                                                                         errmsg = "operands have no common type, in binary operation of " ++ (show ope)
                                                               )
                                                    where
                                                      env' = ty_ovwt_env env1' env2'
      return ((env'', expr_bin_inf), symtbl', err')
    
    _ -> return ((Ty_env [], expr), symtbl, [])


ty_inf :: Symtbl -> Syntree_node -> ExceptT ((Ty_env, Syntree_node), Symtbl, [Error_codes]) IO ((Ty_env, Syntree_node), Symtbl, [Error_codes])
ty_inf symtbl decl =
  case decl of
    Syn_fun_decl fun_id args (Syn_scope (scp_decls, scp_body)) ty -> do
      judge_fun_decl' <- lift (do
                                  judge_fun_decl <- runExceptT $ ty_inf symtbl scp_body
                                  return $ case judge_fun_decl of
                                             Right ((env, scp_body_inf), symtbl', errs) -> let ty' = syn_node_typeof scp_body_inf
                                                                                           in
                                                                                             Right ((env, Syn_fun_decl fun_id args_inf (Syn_scope (scp_decls_inf, scp_body_inf)) ty'),
                                                                                                    symtbl', errs)
                                               where
                                                 args_inf = args
                                                 scp_decls_inf = scp_decls
                                             Left ((env, scp_body_inf), symtbl', errs) -> let ty' = syn_node_typeof scp_body_inf
                                                                                          in
                                                                                            Left ((env, Syn_fun_decl fun_id args_inf (Syn_scope (scp_decls_inf, scp_body_inf)) ty'),
                                                                                                  symtbl', errs)
                                               where
                                                 args_inf = args
                                                 scp_decls_inf = scp_decls
                              )
      case judge_fun_decl' of
        Right judge' -> return judge'
        Left judge' -> throwE judge'
    
    Syn_scope (scp_decls, scp_body) -> do
      judge_scope' <- lift (do
                               judge_scope <- runExceptT $ ty_inf symtbl scp_body
                               return $ case judge_scope of
                                          Right ((env, scp_body_inf), symtbl', errs) -> Right ((env, Syn_scope (scp_decls_inf, scp_body_inf)), symtbl', errs)
                                            where
                                              scp_decls_inf = scp_decls
                                          Left ((env, scp_body_inf), symtbl', errs) -> Left ((env, Syn_scope (scp_decls_inf, scp_body_inf)), symtbl', errs)
                                            where
                                              scp_decls_inf = scp_decls
                           )
      case judge_scope' of
        Right judge' -> return judge'
        Left judge' -> throwE judge'
    
    Syn_expr_seq expr_seq ty_seq ->
      (case expr_seq of
         [] -> return (((Ty_env []), (Syn_expr_seq [] ty_seq)), symtbl, [])
         e:es -> do
           judge_seq' <-
             lift (do
                      judge_seq <- runExceptT $ ty_inf symtbl e
                      case judge_seq of
                        Right ((env, e_inf), symtbl_e, errs_e) ->
                          let ty_inf_seq symtbl (expr, es) = let es'' = case es of
                                                                          [] -> []
                                                                          e:es' -> es'
                                                             in
                                                               do
                                                                 judge_e <- runExceptT $ ty_inf symtbl expr
                                                                 case judge_e of
                                                                   Right ((env, expr_inf), symtbl', errs) -> return $ Right (((env, [expr_inf]), symtbl', errs), es'')
                                                                   Left ((env, expr_inf), symtbl', errs) -> return $ Left (((env, [expr_inf]), symtbl', errs), es'')
                              seq_inf = Prelude.foldl (\judge_seq -> \e_next -> do
                                                          (((env_seq, e_seq), symtbl', errs_seq), es) <- judge_seq
                                                          (((env_next, e_next_inf), symtbl'', errs_next), es') <- (do
                                                                                                                      judge_next <- lift $ ty_inf_seq symtbl' (e_next, es)
                                                                                                                      case judge_next of
                                                                                                                        Right judge' -> return judge'
                                                                                                                        Left judge' ->throwE judge'
                                                                                                                  )
                                                          let ((env_seq', env_next'), equ_env_seq') = ty_overlap_env1 env_seq env_next
                                                          case ty_unif equ_env_seq' of
                                                            Just u_seq' -> do
                                                              let env_seq_inf = ty_subst_env u_seq' env_seq'
                                                                  e_seq' = Prelude.map (syn_node_subst u_seq') e_seq
                                                                  env_next_inf = ty_subst_env u_seq' env_next'
                                                                  e_next_inf' = Prelude.map (syn_node_subst u_seq') e_next_inf
                                                              case (ty_merge_env env_seq_inf env_next_inf) of
                                                                Just env_seq_inf' -> return (((env_seq_inf', (e_seq' ++ e_next_inf')), symtbl'', (errs_seq ++ errs_next)), es')
                                                                Nothing -> throwE (((ty_ovwt_env env_seq_inf env_next_inf, (e_seq' ++ e_next_inf')), symtbl'',
                                                                                    (errs_seq ++ errs_next ++ [Internal_error errmsg])), es')
                                                                  where
                                                                    errmsg = "ill unification detected in type environment construction."
                                                            Nothing -> do
                                                              throwE (((ty_ovwt_env env_seq env_next, (e_seq ++ e_next_inf)), symtbl'',
                                                                       (errs_seq ++ errs_next ++ [Internal_error errmsg])), es')
                                                                where
                                                                  errmsg = "sequential expression type mismmatched,"
                                                      ) (return (((env, [e_inf]), symtbl_e, errs_e), es)) es
                          in
                            do
                              seq_inf' <- runExceptT seq_inf
                              case seq_inf' of
                                Right (((env_seq, seq_body_inf), symtbl', errs_seq), es_remain) ->
                                  let seq_expr_raw = Syn_expr_seq seq_body_inf Ty_unknown
                                  in
                                    if es_remain == [] then
                                      return $ Right ((env_seq, Syn_expr_seq seq_body_inf (syn_retrieve_typeof seq_expr_raw)), symtbl', errs_seq)
                                    else
                                      return $ Left ((env_seq, Syn_expr_seq seq_body_inf (syn_retrieve_typeof seq_expr_raw)), symtbl', (errs_seq ++ [Internal_error errmsg]))
                                  where
                                    errmsg = "inconsistency detected in type inference for sequential expression."
                                Left (((env_seq, seq_body_inf), symtbl', errs_seq), es_remain) -> do
                                  ((env_seq', seq_body_inf'), symtbl'', errs_seq') <- Prelude.foldl (\judge_seq -> \e_next -> do
                                                                                                        ((env_seq, e_seq), symtbl', errs_seq) <- judge_seq
                                                                                                        ((env_next, e_next_inf), symtbl'', errs_next) <-
                                                                                                          (do
                                                                                                              r <- runExceptT $ ty_inf symtbl' e_next
                                                                                                              case r of
                                                                                                                Right r' -> return r'
                                                                                                                Left r' -> return r'
                                                                                                          )
                                                                                                        return ((ty_ovwt_env env_seq env_next, (e_seq ++ [e_next_inf])), symtbl'',
                                                                                                                (errs_seq ++ errs_next))
                                                                                                    ) (return ((env_seq, seq_body_inf), symtbl', errs_seq)) es_remain
                                  let seq_expr_raw = Syn_expr_seq seq_body_inf' Ty_unknown
                                  return $ Left ((env_seq', Syn_expr_seq seq_body_inf' (syn_retrieve_typeof seq_expr_raw)), symtbl'', errs_seq')
                        
                        Left ((env, e_inf), symtbl_e, errs_e) -> return $ Left ((env, e_inf), symtbl_e, errs_e)
                  )
           case judge_seq' of
             Right judge_seq'' -> return judge_seq''
             Left judge_seq'' -> throwE judge_seq''
      )
    
    Syn_val _ _ -> ty_inf_expr symtbl decl
    Syn_var _ _ -> ty_inf_expr symtbl decl
    Syn_expr_asgn _ _ _ -> ty_inf_expr symtbl decl
    Syn_expr_par _ _ -> ty_inf_expr symtbl decl
    
    --Syn_expr_call _ _ _ -> ty_inf_expr symtbl decl
    Syn_expr_call fun_id args ty -> do
      case sym_lkup_fun_decl symtbl fun_id of
        Nothing -> throwE ((Ty_env [], decl), symtbl, [Undefined_symbol errmsg])
          where
            errmsg = "undefined function calling of : " ++ fun_id ++ "."
        Just (Sym_attrib { sym_attr_entity = fun_attr}, symtbl') ->
          (case fun_attr of
             -- func1 (j as int, b as bool) as int { ... }
             -- f_id: func1
             -- f_args: j as int, b as bool
             -- f_body: { ... }
             -- f_ty: Ty_fun [Ty_int, Ty_bool] Ty_int, s.t. "(j as int, b as bool) as int".
             Syn_fun_decl f_id f_args _ (Ty_fun args_ty f_ty)
               | f_id == fun_id -> do
                   judge_call <- lift $
                     let inf_arg symtbl arg_app = runExceptT $
                           case arg_app of
                             Syn_val _ _ -> ty_inf_expr symtbl arg_app
                             Syn_var _ _ -> ty_inf_expr symtbl arg_app
                             Syn_cond_expr _ _ -> ty_inf_expr symtbl arg_app
                             Syn_expr_asgn _ _ _ -> ty_inf_expr symtbl arg_app
                             Syn_expr_par _ _ -> ty_inf_expr symtbl arg_app
                             Syn_expr_call _ _ _ -> ty_inf_expr symtbl arg_app
                             Syn_expr_una _ _ _ -> ty_inf_expr symtbl arg_app
                             Syn_expr_bin _ _ _ -> ty_inf_expr symtbl arg_app
                             -- for Syn_scope, Syn_tydef_decl ,Syn_fun_decl, Syn_arg_decl, Syn_rec_decl, Syn_var_decl, Syn_expr_seq and Syn_none
                             _ -> assert False (
                                    do
                                      errmsg <- return $ __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                      throwE ((Ty_env [], arg_app), symtbl, [Internal_error errmsg])
                                    )
                     in
                       do
                         let make_env_ovwt = Prelude.foldl (\env_whole -> \env -> ty_ovwt_env env_whole env) (Ty_env [])
                             trace_fun_ty (Ty_fun f_args_ty f_ty) args = case f_args_ty of
                                                                           [] -> Right (Ty_fun [] f_ty, args)
                                                                           t:ts -> (case args of
                                                                                      [] -> Right (Ty_fun f_args_ty f_ty, [])
                                                                                      a:as -> if cmp t (syn_node_typeof a) then trace_fun_ty (Ty_fun ts f_ty) as
                                                                                              else Left (Ty_fun f_args_ty f_ty, args)
                                                                                   )
                                                                             where
                                                                               cmp ty1 ty2 = ty1 == ty2
                         args_inf <- Prelude.foldl (\judges_args -> \arg -> do
                                                       r <- judges_args
                                                       case r of
                                                         Right ((js, errs), symtbl, ((f_args_matched, args_matched), f_args_remain)) ->
                                                           (case f_args_remain of
                                                              [] -> return $ Left ((js, errs'), symtbl, ((f_args_matched, args_matched), []))
                                                                where
                                                                  errmsg = "Too many arguments in function calling."
                                                                  errs' = errs ++ [Type_constraint_mismatched errmsg]
                                                              a:as' -> (do
                                                                           arg_inf <- inf_arg symtbl arg
                                                                           case arg_inf of
                                                                             Right (judge_a, symtbl', errs_a) ->
                                                                               return $ Right ((js ++ [judge_a], (errs ++ errs_a)), symtbl',
                                                                                               (((f_args_matched ++ [a]), (args_matched ++ [arg])), as'))
                                                                             Left (judge_a, symtbl', errs_a) ->
                                                                               return $ Left ((js, (errs ++ errs_a)), symtbl',
                                                                                              ((f_args_matched, args_matched), f_args_remain))
                                                                       )
                                                           )
                                                         Left r' -> return r -- omits remaining arguments.
                                                   ) (return $ Right (([], []), symtbl', (([], []), f_args))) args
                         case args_inf of
                           Right ((judges_args, errs_args), symtbl'', ((f_args_matched, acc_args), f_args_remain)) ->
                             return $ case judges_args of
                                        [] -> assert ((f_args_remain == f_args) && (f_args_matched == acc_args) && (acc_args == [])) $
                                                Right ((Ty_env [], Syn_expr_call fun_id [] (Ty_fun args_ty f_ty)), symtbl'', errs_args)
                                        _ -> let env_call = make_env_ovwt (Prelude.map fst judges_args)
                                                 args' = Prelude.map snd judges_args
                                             in
                                               assert ((((length f_args_matched) + (length f_args_remain)) == (length f_args)) && ((length f_args_matched) == (length acc_args)) &&
                                                       ((length acc_args) == (length $ Prelude.map snd judges_args))
                                                      ) $
                                                 let equs_envs = equs_over_envs (Prelude.map fst judges_args)
                                                     equs_args = equs_over_args (Prelude.map syn_node_typeof f_args_matched) args'
                                                 in
                                                   case ty_unif (equs_envs ++ equs_args) of
                                                     Just u_call ->
                                                       let envs_arg_inf = Prelude.map (ty_subst_env u_call) (Prelude.map fst judges_args)
                                                           f_args_inf = Prelude.map (syn_node_subst u_call) f_args
                                                           args_inf = Prelude.map (syn_node_subst u_call) (Prelude.map snd judges_args)
                                                           f_ty_inf = ty_subst u_call f_ty
                                                       in
                                                         case trace_fun_ty (Ty_fun (Prelude.map syn_node_typeof f_args_inf) f_ty_inf) args_inf of
                                                           Right (ty'@(Ty_fun _ f_ty'), args_inf') ->
                                                             assert (args_inf' == []) $
                                                               case (Prelude.foldl (\env_whole -> \env_arg -> do
                                                                                       env_acc <- env_whole
                                                                                       ty_merge_env env_acc env_arg
                                                                                   ) (Just (Ty_env [])) envs_arg_inf
                                                                    ) of
                                                                 Just env_call_inf -> Right ((env_call_inf, Syn_expr_call fun_id args_inf ty'), symtbl'', errs_args)
                                                                 Nothing -> let env_call_inf = make_env_ovwt envs_arg_inf
                                                                            in
                                                                              assert False (
                                                                                do
                                                                                  errmsg <-  return $ __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                                  Left ((env_call_inf, Syn_expr_call fun_id f_args_inf ty'), symtbl'', (errs_args ++ [Internal_error errmsg]))
                                                                                )
                                                           Left (ty'@(Ty_fun _ f_ty'), _) ->
                                                             let env_call_inf = make_env_ovwt envs_arg_inf
                                                             in
                                                               assert False (
                                                                 do
                                                                   errmsg <- return $ __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                   Left ((env_call_inf, Syn_expr_call fun_id args_inf ty'), symtbl'', (errs_args ++ [Internal_error errmsg]))
                                                                 )
                                                     Nothing ->
                                                       let ty_and_args = zip (Prelude.map syn_node_typeof f_args) args'
                                                       in
                                                         case (Prelude.foldl (\acc -> \(env, (ty, arg)) -> do
                                                                                 ((envs_acc, ty_args_acc), substs) <- acc
                                                                                 let ty_args_acc' = ty_args_acc ++ [(ty, arg)]
                                                                                 let envs_acc' = envs_acc ++ [env]
                                                                                     equs_envs = equs_over_envs envs_acc'
                                                                                 let ty_acc' = Prelude.map fst ty_args_acc'
                                                                                     args_acc' = Prelude.map snd ty_args_acc'
                                                                                     equs_args = equs_over_args ty_acc' args_acc'
                                                                                 case ty_unif (equs_envs ++ equs_args) of
                                                                                   Just u_call -> Right ((envs_acc', ty_args_acc'), u_call:substs)
                                                                                   Nothing -> Left (((envs_acc, ty_args_acc), substs), (env, (ty, arg)), [Type_constraint_mismatched errmsg])
                                                                                     where
                                                                                       errmsg = "incompatible type on passing " ++ (show $ (length substs) + 1) ++ " th" ++
                                                                                                " argument to the function of " ++ f_id ++ "."
                                                                             ) (Right (([], []), [])) (zip (Prelude.map fst judges_args) ty_and_args)
                                                              ) of
                                                           Right ((envs_acc, ty_args_acc), substs) ->
                                                             assert False ( -- Its also seems to be internal error, for the fact that whole unification had even failed above.
                                                               do
                                                                 errmsg <- return $ __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                 result (envs_acc, ty_args_acc) substs [Internal_error errmsg]
                                                               )
                                                           Left (((envs_acc, ty_args_acc), substs), _, errs) -> result (envs_acc, ty_args_acc) substs errs
                                                       where
                                                         result (envs_acc, ty_args_acc) substs errs =
                                                           let args_acc = Prelude.map snd ty_args_acc
                                                           in
                                                             assert ((length envs_acc) == (length args_acc)) $
                                                               case substs of
                                                                 [] -> let env_call = make_env_ovwt envs_acc
                                                                           ty' = case trace_fun_ty (Ty_fun (Prelude.map syn_node_typeof f_args) f_ty) args_acc of
                                                                                   Right (ty@(Ty_fun _ f_ty'), _) -> ty
                                                                                   Left (ty@(Ty_fun _ f_ty'), _) -> ty
                                                                       in
                                                                         Left ((env_call, Syn_expr_call fun_id args_acc ty'), symtbl'', (errs_args ++ errs))
                                                                 s:_ -> let envs_arg_inf = Prelude.map (ty_subst_env s) envs_acc
                                                                            ty_args_inf = Prelude.map (ty_subst s) (Prelude.map syn_node_typeof f_args)
                                                                            args_inf = Prelude.map (syn_node_subst s) args_acc
                                                                            f_ty_inf = ty_subst s f_ty
                                                                        in
                                                                          let env_call_inf = make_env_ovwt envs_arg_inf
                                                                              ty' = case trace_fun_ty (Ty_fun ty_args_inf f_ty_inf) args_inf of
                                                                                      Right (ty@(Ty_fun _ f_ty'), _) -> ty
                                                                                      Left (ty@(Ty_fun _ f_ty'), _) -> ty
                                                                          in
                                                                            Left ((env_call_inf, Syn_expr_call fun_id args_inf ty'), symtbl'', (errs_args ++ errs))
                                          where
                                            equs_over_envs envs =
                                              case group_binds ([], (union_binds envs)) of
                                                (b_groups, remains) -> assert ((length remains) == 0) $ gen_equs b_groups
                                            equs_over_args ty_params args =
                                              let ty_args = Prelude.map syn_node_typeof args
                                              in
                                                let equs = zip ty_params ty_args
                                                    equs' = Prelude.foldl (\es -> \(ty_p, ty_a) -> es ++ (if (ty_p == ty_a) then [] else [(ty_p, ty_a)])) [] equs
                                                in
                                                  assert ((length ty_params) == (length ty_args)) equs'
                                            union_binds envs =
                                              case envs of
                                                [] -> []
                                                (Ty_env []):es -> union_binds es
                                                (Ty_env bs):es -> Set.toList $ Set.union (Set.fromList bs) (Set.fromList (union_binds es))
                                            group_binds (groups, remains) =
                                              case remains of
                                                [] -> (groups, [])
                                                (var, _):bs -> group_binds ((groups ++ [new_group]), remains')
                                                  where
                                                    (new_group, remains') = Prelude.foldl (\(picks, drops) -> \e@(v_id, _) -> if v_id == var then (picks ++ [e], drops)
                                                                                                                              else (picks, drops ++ [e])
                                                                                          ) ([], []) remains
                                            gen_equs b_groups =
                                              case b_groups of
                                                [] -> []
                                                [b]:gs -> gen_equs gs
                                                g:gs -> (enum_equs g) ++ (gen_equs gs)
                                                  where
                                                    enum_equs binds =
                                                      case binds of
                                                        [] -> []
                                                        (v_id, ty):bs ->
                                                          let equs = Prelude.foldl (\es -> \(v_id', ty') -> assert (v_id' == v_id) (if (ty' == ty) then (es ++ [(ty, ty')]) else es)) [] bs
                                                          in
                                                            equs ++ (enum_equs bs)
                           Left ((judges_args, errs_args), symtbl'', ((f_args_matched, acc_args), f_args_remain)) ->
                             let args_ty = Prelude.foldl (\a_ts -> \a -> (a_ts ++ [syn_node_typeof a])) [] f_args_remain
                             in
                               return $ case judges_args of
                                          [] -> assert ((f_args_remain == f_args) && (f_args_matched == acc_args) && (acc_args == [])) $
                                                  Left ((Ty_env [], Syn_expr_call fun_id [] (Ty_fun args_ty f_ty)), symtbl'', errs_args)
                                          _ -> assert ((((length f_args_matched) + (length f_args_remain)) == (length f_args)) && (f_args_matched == acc_args) &&
                                                       ((length judges_args) == (length acc_args))
                                                      ) $ Left ((env_call_inf, Syn_expr_call fun_id args_inf (Ty_fun args_ty f_ty)), symtbl'', errs_args)
                                            where
                                              (env_call_inf, args_inf) = merge_by_ovwt judges_args
                                              merge_by_ovwt judges = case judges of
                                                [] -> (Ty_env [], [])
                                                (env, expr):js -> (ty_ovwt_env envs env, (expr:exprs))
                                                  where
                                                    (envs, exprs) = merge_by_ovwt js
                   case judge_call of
                     Right judge' -> return judge'
                     Left judge' -> throwE judge'
             _ -> throwE ((Ty_env [], decl), symtbl', [Type_constraint_mismatched errmsg])
               where
                 errmsg = "Function calling must be applied on function objects."
          )
        Just _ -> assert False (
                    do
                      let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                      throwE ((Ty_env [], decl), symtbl, [Internal_error errmsg])
                    )
    Syn_cond_expr _ _ -> ty_inf_expr symtbl decl
    Syn_expr_una _ _ _ -> ty_inf_expr symtbl decl
    Syn_expr_bin _ _ _ -> ty_inf_expr symtbl decl
    
    --case Syn_tydef_decl _ _ -> INTERNAL ERROR
    --case Syn_arg_decl _ _ -> INTERNAL ERROR
    --case Syn_rec_decl _ _ -> INTERNAL ERROR
    --case Syn_var_decl _ _ -> INTERNAL ERROR
    
    _ -> return ((Ty_env [], decl), symtbl, []) -- Syn_none


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
  

  let (tokens, src_remains) = conv2_tokens src
  --assert False $ putStrLn $ "source:  " ++ (show src)
  putStrLn $ "source:  " ++ (show src)
  putStrLn $ "tokens:  " ++ (show (tokens, src_remains))
  
  symtbl <- return $ sym_enter_scope Nothing Sym_cat_decl
  
  {- (syn_forest, symtbl', tokens')  <- return $ case src_remains of
                                                "" -> let (syn_tree, symtbl', tokens') = cons_ptree symtbl tokens (True, True, True)
                                                      in
                                                        case syn_tree of
                                                          Just s_tree -> let (s_ts, symtbl'', tokens'') = cons_p_trees symtbl' tokens'
                                                                         in
                                                                           (Just (s_tree:s_ts), symtbl'', tokens'')
                                                          _ -> (Nothing, symtbl', tokens')
                                                  where
                                                    cons_p_trees symtbl [] = ([], symtbl, [])
                                                    cons_p_trees symtbl (Tk_smcl:ts) =
                                                      let (syn_tree, symtbl', ts') = cons_ptree symtbl ts (True, True, True)
                                                      in
                                                        case syn_tree of
                                                          Just s_tree -> let (s_trees, symtbl'', ts'') = cons_p_trees symtbl' ts'
                                                                         in
                                                                           (s_tree:s_trees, symtbl'', ts'')
                                                          _ -> ([], symtbl', ts')
                                                    cons_p_trees symtbl ts = ([], symtbl, ts)
                                                _ -> (Nothing, symtbl, tokens) -}
  (syn_forest, symtbl', tokens') <- do
    r <- (case src_remains of
            "" -> do
              r <- runExceptT $ cons_ptree1 symtbl tokens (True, True, True)
              case r of
                Left err -> (do
                                print_excepts err
                                return $ Left ()
                            )
                Right (syn_tree, symtbl', tokens') -> (case syn_tree of
                                                         Just s_tree -> do
                                                           r_ts <- cons_p_trees symtbl' tokens'
                                                           case r_ts of
                                                             Left () -> return $ Left ()
                                                             Right (s_ts, symtbl'', tokens'') -> return $ Right (Just (s_tree:s_ts), symtbl'', tokens'')
                                                         _ -> return $ Right (Nothing, symtbl', tokens')
                                                      )
                  where
                    cons_p_trees symtbl tokens =
                      case tokens of
                        [] -> return $ Right ([], symtbl, [])
                        (Tk_smcl:ts) -> do
                          r <- runExceptT $ cons_ptree1 symtbl ts (True, True, True)
                          case r of
                            Left err -> (do
                                            print_excepts err
                                            return $ Left ()
                                        )
                            Right (syn_tree, symtbl', ts') -> (case syn_tree of
                                                                 Just s_tree -> do
                                                                   r_ts <- cons_p_trees symtbl' ts'
                                                                   case r_ts of
                                                                     Left () -> return $ Left ()
                                                                     Right (s_trees, symtbl'', ts'') -> return $ Right (s_tree:s_trees, symtbl'', ts'')
                                                                 _ -> return $ Right ([], symtbl', ts')
                                                              )
                        ts -> return $ Right ([], symtbl, ts)
            _ -> return $ Right (Nothing, symtbl, tokens)
         )
    case r of
      Left _ -> return (Nothing, symtbl, tokens)
      Right r' -> return r'
  putStrLn $ "p-trees: " ++ (show (syn_forest, tokens'))
  
  putStr "ty-raw:  "
  ty_curved <- case syn_forest of
                 Just s_trees -> do
                   r <- runMaybeT $ Prelude.foldl (\stmts_tv -> (\stmt -> do
                                                                    (stmts, prev_tv) <- stmts_tv
                                                                    r' <- lift (do
                                                                                   r_cur <- runExceptT $ ty_curve (stmt, prev_tv)
                                                                                   case r_cur of
                                                                                     Left err -> (do
                                                                                                     putStrLn errmsg
                                                                                                     return $ Nothing
                                                                                                 )
                                                                                       where
                                                                                         errmsg = case err of
                                                                                                    Error_Excep Excep_assert_failed assert_msg -> assert_msg
                                                                                                    Error_Excep _ errmsg -> errmsg
                                                                                     Right (stmt', prev_tv') -> return $ Just (stmts ++ [stmt'], prev_tv')
                                                                               )
                                                                    case r' of
                                                                      Nothing -> mzero
                                                                      Just (stmts', crnt_tv) -> return (stmts', crnt_tv)
                                                                )
                                                  ) (return ([], initial_flesh_tvar)) s_trees
                   case r of
                     Nothing -> return []
                     Just (s_trees', _) -> return s_trees'
  mapM_ putStrLn $ Prelude.map show ty_curved
  
  putStr "ty-inf:  "
  (judges_inf, symtbl'', errs) <- do
    r <- runExceptT $ Prelude.foldl (\js -> \t_raw -> do
                                        (judges, symtbl, errs) <- js
                                        ((env, t_inf), symtbl', errs') <- ty_inf symtbl t_raw
                                        return (case judges of
                                                  [] -> ([(env, t_inf)], symtbl', (errs ++ errs'))
                                                  _ -> ((judges ++ [(env, t_inf)]), symtbl', (errs ++ errs'))
                                               )
                                    ) (return ([], symtbl', [])) ty_curved
    return (case r of
              Right r -> r
              Left ((env, t_inf), symtbl', errs) -> ([(env, t_inf)], symtbl', errs)
           )
  mapM_ putStrLn $ Prelude.map show judges_inf
  
  putStr "simtbl:  "
  putStrLn $ show (sym_func symtbl'')
  
    where
      read_src :: Handle -> IO String
      read_src h = do
        eof <- hIsEOF h
        if eof then return []
          else do
          str <- hGetLine h
          str' <- read_src h
          return $ str ++ str'
      
      print_excepts :: Error_Excep -> IO ()
      print_excepts err = do
        let errmsg = case err of
                       Error_Excep Excep_assert_failed assert_msg -> assert_msg
                       Error_Excep _ errmsg -> errmsg
        putStrLn errmsg
        return ()
