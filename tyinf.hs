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
import Data.Maybe
import Data.Either (isLeft, isRight)
import Data.Map as M
import Data.Set as Set
import Control.Monad
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

data Sym_category =
  Sym_cat_typedef
  | Sym_cat_record
  | Sym_cat_func
  | Sym_cat_decl
  deriving (Eq, Ord, Show)

type Row = Integer
type Col = Integer
data Sym_attrib =
  Sym_attrib {sym_attr_geometry :: (Row, Col), sym_attr_entity :: Syntree_node}
  deriving (Eq, Ord, Show)

data Symtbl_node =
  Sym_entry {sym_key :: Integer, sym_ident :: String, sym_attr :: Sym_attrib}
  deriving (Eq, Ord, Show)

data Symtbl_cluster =
  Sym_empty
  | Sym_add Symtbl_node Symtbl_cluster
  deriving (Eq, Ord, Show)

data Symtbl_anon_ident =
  Symtbl_anon_ident {sym_anon_var :: Integer, sym_anon_record :: Integer}
  deriving (Eq, Ord, Show)

type Scope_id = (Integer, Integer)
type Scope_Lv = Integer
data Sym_tbl =
  Scope_empty
  | Scope_add (Scope_id, Scope_Lv, Symtbl_anon_ident, Symtbl_cluster) Sym_tbl
  deriving (Eq, Ord, Show)
sym_crnt_level :: Sym_tbl -> Scope_Lv
sym_crnt_level Scope_empty = 0
sym_crnt_level (Scope_add (_, lv, _, _ ) _) = lv

type Syms_stack = (Maybe Sym_tbl, Sym_tbl)
sym_scope_left :: Syms_stack -> Maybe Sym_tbl
sym_scope_left (left, right) = left
sym_scope_right :: Syms_stack -> Sym_tbl
sym_scope_right (left, right) = right

data Symtbl =
  Symtbl {sym_typedef :: (Syms_stack, Integer), sym_record :: (Syms_stack, Integer), sym_func :: (Syms_stack, Integer), sym_decl :: (Syms_stack, Integer), fresh_tvar :: Fresh_tvar}
  deriving (Eq, Ord, Show)

sym_internalerr :: [Error_codes] -> ([Error_codes], [Error_codes])
sym_internalerr err =
  case err of
    [] -> ([], [])
    e:es -> (case sym_internalerr es of
               (es_fatal, es_others) -> (case e of
                                           Internal_error _ -> (e:es_fatal, es_others)
                                           _ -> (es_fatal, e:es_others)
                                        )
            )

sym_categorize' :: Symtbl -> Sym_category -> (Syms_stack, Integer)
sym_categorize' symtbl cat =
  ras_trace "in sym_categorize" (
  case cat of
    Sym_cat_typedef -> sym_typedef symtbl
    Sym_cat_record -> sym_record symtbl
    Sym_cat_func -> sym_func symtbl
    Sym_cat_decl -> sym_decl symtbl
  )
sym_categorize :: Symtbl -> Sym_category -> Syms_stack
sym_categorize symtbl cat =
  ras_trace "in sym_categorize" (
  fst $ sym_categorize' symtbl cat
  )

sym_adjust_tvar :: Symtbl -> Fresh_tvar -> Symtbl
sym_adjust_tvar symtbl next_fresh_tv =
  ras_trace "in sym_adjust_tvar" (
  symtbl{fresh_tvar = next_fresh_tv}
  )

sym_update :: Symtbl -> Sym_category -> (Syms_stack, Integer) -> Symtbl
sym_update symtbl cat tbl =
  ras_trace "in sym_update" (
  case cat of
    Sym_cat_typedef -> symtbl{sym_typedef = tbl}
    Sym_cat_func -> symtbl{sym_func = tbl}
    Sym_cat_record -> symtbl{sym_record = tbl}
    Sym_cat_decl -> symtbl{sym_decl = tbl}
  )

sym_leave_scope :: Symtbl -> Sym_category -> (Symtbl, [Error_codes])
sym_leave_scope symtbl cat =
  ras_trace "in sym_leave_scope" (
  let (stbl, last_id) = sym_categorize' symtbl cat
  in
    let (stbl', err) = case stbl of
                         (left, Scope_empty) -> (stbl, err')
                           where
                             err' = case left of
                                      Nothing -> []
                                      _ -> [Internal_error errmsg]
                                        where
                                          errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                         (left, Scope_add crnt prev) -> (case left of
                                                            Nothing -> ((Just (Scope_add crnt Scope_empty), prev), [])
                                                            Just left' -> ((Just (Scope_add crnt left'), prev), [])
                                                        )
    in
      (sym_update symtbl cat (stbl', last_id), err)
  )

sym_enter_scope :: Maybe Symtbl -> Sym_category -> (Symtbl, [Error_codes])
sym_enter_scope symtbl cat =
  ras_trace "in sym_enter_scope" (
  case symtbl of
    Just sym_tbl -> let (stbl, last_id) = sym_categorize' sym_tbl cat
                    in
                      let (stbl', err) =
                            case stbl of
                              (left, Scope_empty) -> ((left, Scope_add ((0, last_id + 1), 1, Symtbl_anon_ident {sym_anon_var = 1, sym_anon_record = 1}, Sym_empty) Scope_empty), [])
                              (left, r@(Scope_add ((_, id), lv, sym_anon_ident, _) _)) -> ((left, Scope_add ((id, last_id + 1), lv + 1, sym_anon_ident, Sym_empty) r), [])
                      in
                        (sym_update sym_tbl cat (stbl', last_id + 1), err)
    Nothing -> let symtbl0 = Symtbl {sym_typedef = sym_typdef0, sym_record = sym_record0, sym_func = sym_func0, sym_decl = sym_decl, fresh_tvar = fresh_tvar_initial}
               in
                 sym_enter_scope (Just symtbl0) cat
      where
        sym_typdef0 = ((Nothing, Scope_empty), 0)
        sym_record0 = ((Nothing, Scope_empty), 0)
        sym_func0 = ((Nothing, Scope_empty), 0)
        sym_decl = ((Nothing, Scope_empty), 0)
  )

sym_new_anonid_var :: Symtbl -> Sym_category -> (String, String, String) -> ((String, Symtbl), [Error_codes])
sym_new_anonid_var symtbl cat (prefx, sufix, sep) =
  ras_trace "in sym_new_anonid_var" (
  let d2s_var m = "var_" ++ ((prefx ++ sep) ++ (show m) ++ (sep ++ sufix))
      (stbl, last_id) = sym_categorize' symtbl cat
  in
    let ((stbl', last_id'), err) = (case stbl of
                                      (_, Scope_empty) -> (sym_categorize' symtbl' cat, err')
                                        where
                                          (symtbl', err') = sym_enter_scope (Just symtbl) cat
                                      (_, Scope_add _ _) -> ((stbl, last_id), [])
                                   )
    in
      let (anonid, stbl'') = case stbl' of
                               (left, Scope_add (id, lv, anon_crnt@(Symtbl_anon_ident {sym_anon_var = top}), syms) stbls') ->
                                 ((d2s_var top), (left, Scope_add (id, lv, anon_crnt {sym_anon_var = top + 1}, syms) stbls'))
      in
        ((anonid, sym_update symtbl cat (stbl'', last_id')), err)
  )

sym_new_anonid_rec :: Symtbl -> Sym_category -> (String, String, String) -> ((String, Symtbl), [Error_codes])
sym_new_anonid_rec symtbl cat (prefx, sufix, sep) =
  ras_trace "in sym_new_anonid_rec" (
  let d2s_rec m = "rec_" ++ ((prefx ++ sep) ++ (show m) ++ (sep ++ sufix))
      (stbl, last_id) = sym_categorize' symtbl cat
  in
    let ((stbl', last_id'), err) = (case stbl of
                                      (_, Scope_empty) -> (sym_categorize' symtbl' cat, err')
                                        where
                                          (symtbl', err') = sym_enter_scope (Just symtbl) cat
                                      (_, Scope_add _ _) -> ((stbl, last_id), [])
                                   )
    in
      let (anonid, stbl'') = case stbl' of
                               (left, Scope_add (id, lv, anon_crnt@(Symtbl_anon_ident {sym_anon_record = top}), syms) stbls') ->
                                 ((d2s_rec top), (left, Scope_add (id, lv, anon_crnt {sym_anon_record = top + 1}, syms) stbls'))
      in
        ((anonid, sym_update symtbl cat (stbl'', last_id')), err)
  )

sym_combine :: Sym_tbl -> Sym_tbl -> Sym_tbl
sym_combine tbl1@(Scope_add (id_1, lv_1, anon_idents_1, syms_1) tbl1') tbl2@(Scope_add (id_2, lv_2, anon_idents_2, syms_2) tbl2') =
  ras_trace "in sym_combine" (
  case tbl1' of
    Scope_empty ->
      (case syms_1 of
         Sym_empty -> (case syms_2 of
                         Sym_empty -> tbl2'
                         _ -> tbl2
                      )
         _ -> (case syms_2 of
                 Sym_empty -> Scope_add (id_1, lv_1, anon_idents_1, syms_1) tbl2'
                 _ -> Scope_add (id_1, lv_1, anon_idents_1, (cat syms_1 syms_2)) tbl2'
              )
      )
      where
        cat :: Symtbl_cluster -> Symtbl_cluster -> Symtbl_cluster
        cat (Sym_add sym syms1') syms2 =
          case syms1' of
            Sym_empty -> Sym_add sym syms2
            _ -> Sym_add sym (cat syms1' syms2)
            
    _ -> Scope_add (id_1, lv_1, anon_idents_1, syms_1) (sym_combine tbl1' tbl2)
  )

sym_search :: Sym_tbl -> String -> (Maybe (Sym_attrib, (Sym_tbl, Sym_tbl)), [Error_codes])
sym_search sym_tbl ident =
  ras_trace "in sym_search" (
  let walk syms ident =
        case syms of
          Sym_empty -> Nothing
          Sym_add sym syms' -> if ((sym_ident sym) == ident) then Just (sym, (Sym_empty, syms))
                               else case (walk syms' ident) of
                                      Nothing -> Nothing
                                      Just (cand, (pasts, remains)) -> Just (cand, (Sym_add sym pasts, remains))
  in
    case sym_tbl of
      Scope_empty -> (Nothing, [])
      Scope_add (id, lv, anon_idents, syms) sym_tbl' -> (case (walk syms ident) of
                                                           Just (cand, (pasts, remains)) -> (Just ((sym_attr cand), (pasts', remains')), [])
                                                             where
                                                               pasts' = Scope_add (id, lv, anon_idents, pasts) Scope_empty
                                                               remains' = Scope_add (id, lv, anon_idents, remains) sym_tbl'
                                                           Nothing -> (case sym_search sym_tbl' ident of
                                                                         (Just (cand, (pasts, remains)), err) -> (Just (cand, (Scope_add (id, lv, anon_idents, syms) pasts, remains)), err)
                                                                         (Nothing, err) -> (Nothing, err)
                                                                      )
                                                        )
  )

sym_find :: Symtbl -> Sym_category -> (Maybe Integer, Integer) -> ((Maybe (String, Sym_attrib), Symtbl), [Error_codes])
sym_find symtbl cat (scope_id, entry_id) =
  ras_trace "in sym_find" (
  let ((sym_tbl_l, sym_tbl_r), last_id) = sym_categorize' symtbl cat
  in
    case sym_tbl_l of
      Nothing -> ((Nothing, symtbl), [])
      Just stbl_l -> (case stbl_l of
                        Scope_empty -> ((Nothing, symtbl), [])
                        Scope_add ((_, id), lv, anon_idents, syms) sym_tbl_l' ->
                          (case scope_id of
                             Just scp_id -> if id /= scp_id then (case sym_find symtbl' cat (scope_id, entry_id) of
                                                                    ((r, _), err) | err == [] -> ((r, symtbl), [])
                                                                    ((r, _), err) -> ((r, symtbl), err ++ [Internal_error errmsg])
                                                                      where
                                                                        errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                 )
                                            else
                                              case search syms entry_id of
                                                ((r, _), err) -> if err == [] then ((r, symtbl), [])
                                                                 else ((r, symtbl), err ++ [Internal_error errmsg])
                                                  where
                                                    errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                             Nothing -> (case search syms entry_id of
                                           ((r, _), err) -> if err == [] then ((r, symtbl), [])
                                                            else
                                                              ((r, symtbl), err ++ [Internal_error errmsg])
                                             where
                                               errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                        )
                          )
                          where
                            symtbl' = sym_update symtbl cat (((case sym_tbl_l' of
                                                                 Scope_empty -> Nothing
                                                                 _ -> Just sym_tbl_l'), sym_tbl_r), last_id)
                            search :: Symtbl_cluster -> Integer -> ((Maybe (String, Sym_attrib), Symtbl), [Error_codes])
                            search syms entry_id = case walk syms entry_id of
                                                     Nothing -> sym_find symtbl' cat (scope_id, entry_id)
                                                     Just (Sym_entry {sym_key = key, sym_ident = ident, sym_attr = attr}) | key == entry_id -> ((Just (ident, attr), symtbl), [])
                                                     _ -> ((Nothing, symtbl), [Internal_error errmsg])
                                                       where
                                                         errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                     )
        where
          walk :: Symtbl_cluster -> Integer -> Maybe Symtbl_node
          walk syms id  = case syms of
                            Sym_empty -> Nothing
                            Sym_add sym @(Sym_entry {sym_key = key}) syms' -> if key == id then Just sym
                                                                              else walk syms' id
  )

type Sym_handle = (Sym_category, (Sym_tbl, Sym_tbl))
sym_lookup :: Symtbl -> (Sym_category, Syntree_node -> Bool) -> String -> (Maybe ((Sym_attrib, (Sym_category, (Sym_tbl, Sym_tbl))), Symtbl), [Error_codes])
sym_lookup symtbl (cat, declp) ident =
  ras_trace "in sym_lookup" (
  let ((left, stbl), last_id) = sym_categorize' symtbl cat
  in
    case sym_search stbl ident of
      (Nothing, err) -> (Nothing, err)
      (Just (attr, h@(past, remains)), err) -> if declp (sym_attr_entity attr) then (Just ((attr, (cat, h)), symtbl), err)
                                               else
                                                 let remains' = case remains of
                                                                  Scope_add (_, _, _, Sym_empty) ps -> ps
                                                                  Scope_add (_, _, _, Sym_add s Sym_empty) ps -> ps
                                                                  Scope_add (id, lv, anon_idents, Sym_add s ss) ps -> Scope_add (id, lv, anon_idents, ss) ps
                                                 in
                                                   case sym_lookup (sym_update symtbl cat ((left, remains'), last_id)) (cat, declp) ident of
                                                     (Just ((attr, (cat', (past', remains''))), _), err) | cat' == cat -> (Just ((attr, (cat', (past'', remains''))), symtbl'), err)
                                                       where
                                                         past'' = sym_combine past past'
                                                         symtbl' = sym_update symtbl cat ((left, sym_combine past'' remains''), last_id)
                                                     (Just ((attr, (cat', (past', remains''))), _), err) -> (Just ((attr, (cat', (past'', remains''))), symtbl'), err')
                                                       where
                                                         past'' = sym_combine past past'
                                                         symtbl' = sym_update symtbl cat ((left, sym_combine past'' remains''), last_id)
                                                         err' = err ++ [Internal_error errmsg]
                                                           where
                                                             errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                     (Nothing, err) -> (Nothing, err)
  )

sym_lkup_tydef_decl :: Symtbl -> String -> (Maybe ((Sym_attrib, (Sym_category, (Sym_tbl, Sym_tbl))), Symtbl), [Error_codes])
sym_lkup_tydef_decl symtbl ident =
  ras_trace "in sym_lkup_tydef_decl" (
  let declp a = case a of
                  Syn_tydef_decl _ _ -> True
                  _ -> False
  in
    case sym_lookup symtbl (Sym_cat_typedef, declp) ident of
      r@(Just ((_, (_, _)), symtbl'), err) | verify symtbl symtbl' -> r
        where
          verify :: Symtbl -> Symtbl -> Bool
          verify symtbl symtbl' = (sym_categorize' symtbl Sym_cat_typedef) == (sym_categorize' symtbl' Sym_cat_typedef)
      (r@(Just ((_, (_, _)), symtbl')), err) -> (r, err ++ [Internal_error errmsg])
        where
          errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
      (Nothing, err) -> (Nothing, err)
  )

sym_lkup_fun_decl :: Symtbl -> String -> (Maybe ((Sym_attrib, (Sym_category, (Sym_tbl, Sym_tbl))), Symtbl), [Error_codes])
sym_lkup_fun_decl symtbl ident =
  ras_trace "in sym_lkup_fun_decl" (
  let declp a = case a of
                  Syn_fun_decl' _ _ _ _ -> True
                  _ -> False
      
  in
    case sym_lookup symtbl (Sym_cat_decl, declp) ident of
      r@(Just ((_, (_, _)), symtbl'), err) | verify symtbl symtbl' -> r
        where
          verify :: Symtbl -> Symtbl -> Bool
          verify symtbl symtbl' = (sym_categorize' symtbl Sym_cat_decl) == (sym_categorize' symtbl' Sym_cat_decl)
      (r@(Just ((_, (_, _)), symtbl')), err) -> (r, err ++ [Internal_error errmsg])
        where
          errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
      (Nothing, err) -> (case sym_lookup symtbl (Sym_cat_func, declp) ident of
                           (r'@(Just ((_, (_, _)), symtbl'')), err') | verify' symtbl symtbl'' -> (r', err ++ err')
                             where
                               verify' :: Symtbl -> Symtbl -> Bool
                               verify' symtbl symtbl' = (sym_categorize' symtbl Sym_cat_func) == (sym_categorize' symtbl' Sym_cat_func)
                           (r'@(Just ((_, (_, _)), symtbl'')), err') -> (r', err ++ err' ++ [Internal_error errmsg])
                             where
                               errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                           (Nothing, err') -> (Nothing, err ++ err')
                        )
  )

sym_lkup_rec_decl :: Symtbl -> String -> (Maybe ((Sym_attrib, (Sym_category, (Sym_tbl, Sym_tbl))), Symtbl), [Error_codes])
sym_lkup_rec_decl symtbl ident =
  ras_trace "in sym_lkup_rec_decl" (
  let declp a = case a of
                  Syn_rec_decl _ _ -> True
                  _ -> False
  in
    case sym_lookup symtbl (Sym_cat_record, declp) ident of
      r@(Just ((_, (_, _)), symtbl'), err) | verify symtbl symtbl' -> r
        where
          verify :: Symtbl -> Symtbl -> Bool
          verify symtbl symtbl' = (sym_categorize' symtbl Sym_cat_record) == (sym_categorize' symtbl' Sym_cat_record)
      (r@(Just ((_, (_, _)), symtbl')), err) -> (r, err ++ [Internal_error errmsg])
        where
          errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
      (Nothing, err) -> (Nothing, err)
  )

sym_lkup_var_decl :: Symtbl -> String -> (Maybe ((Sym_attrib, (Sym_category, (Sym_tbl, Sym_tbl))), Symtbl), [Error_codes])
sym_lkup_var_decl symtbl ident =
  ras_trace "in sym_lkup_var_decl" (
  let declp a = case a of
                  Syn_var_decl _ _ -> True
                  _ -> False
  in
    case sym_lookup symtbl (Sym_cat_decl, declp) ident of
      r@(Just ((_, (_, _)), symtbl'), err) | verify symtbl symtbl' -> r
        where
          verify :: Symtbl -> Symtbl -> Bool
          verify symtbl symtbl' = (sym_categorize' symtbl Sym_cat_decl) == (sym_categorize' symtbl' Sym_cat_decl)
      (r@(Just ((_, (_, _)), symtbl')), err) -> (r, err ++ [Internal_error errmsg])
        where
          errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
      (Nothing, err) -> (Nothing, err)
  )

sym_modify :: (Symtbl, (Sym_category, (Sym_tbl, Sym_tbl))) -> String -> Sym_attrib -> (Maybe ((Sym_attrib, (Sym_category, (Sym_tbl, Sym_tbl))), Symtbl), [Error_codes])
sym_modify (symtbl, (cat, (top, btm))) ident attr_new =
  ras_trace "in sym_modify" (
  let errmsg = ""
      ((left, sym_tbl), last_id) = sym_categorize' symtbl cat
  in    
    if (sym_combine top btm) /= sym_tbl then let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                             in
                                               (Nothing, [Internal_error errmsg])
    else
      case btm of
        Scope_empty -> (Nothing, [Internal_error errmsg])
          where
            errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
        Scope_add (_, _, _, Sym_empty) ps -> (Nothing, [Internal_error errmsg])
          where
            errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
        Scope_add (id, lv, anon_idents, Sym_add s ss) ps -> (case modify s attr_new of
                                                               Right s' -> (Just ((sym_attr s', (cat, (top, btm'))), symtbl'), [])
                                                                 where
                                                                   btm' = Scope_add (id, lv, anon_idents, Sym_add s' ss) ps
                                                                   symtbl' = sym_update symtbl cat ((left, sym_combine top btm'), last_id)
                                                               Left err -> (Nothing, err ++ [Internal_error errmsg])
                                                                 where
                                                                   errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                            )
          where
            modify :: Symtbl_node -> Sym_attrib -> Either [Error_codes] Symtbl_node
            modify sym attr_new =
              case sym of
                Sym_entry{sym_ident = id, sym_attr = attr} | id == ident ->
                                                               (case attr_new of
                                                                  Sym_attrib {sym_attr_geometry = (-1, -1), sym_attr_entity = new_entity} -> Right sym{sym_attr = attr'}
                                                                    where
                                                                      attr' = attr{sym_attr_entity = new_entity}
                                                                  _ -> Left [Internal_error errmsg]
                                                                    where
                                                                      errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                               )
                _ -> Left [Internal_error errmsg]
                  where
                    errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
  )

cmp_entity :: Symtbl_node -> Syntree_node -> Bool
cmp_entity (Sym_entry {sym_attr = attr}) entity =
  case (sym_attr_entity attr) of
    Syn_tydef_decl _ _ -> (case entity of
                             Syn_tydef_decl _ _ -> True
                             _ -> False
                          )
    Syn_fun_decl' _ _ _ _ -> (case entity of
                                Syn_fun_decl' _ _ _ _ -> True
                                _ -> False
                             )
    Syn_arg_decl _ _ -> (case entity of
                           Syn_arg_decl _ _ -> True
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

{- sym_regist :: Bool -> Symtbl -> Sym_category -> (String, Syntree_node) -> (Symtbl, [Error_codes])
sym_regist ovwt symtbl cat (ident, entity) =
  ras_trace "in sym_regist" (
  let reg_sym (sym_tbl, last_id) (ident, sym) =
        case sym_tbl of
          Scope_empty -> ((Scope_add ((0, last_id + 1), 0, Symtbl_anon_ident {sym_anon_var = 1, sym_anon_record = 1}, (Sym_add sym Sym_empty)) Scope_empty), last_id + 1, [])
          Scope_add (id, lv, anon_idents, syms) scps -> (case syms of
                                                           Sym_empty -> ((Scope_add (id, lv, anon_idents, (Sym_add sym Sym_empty)) scps), last_id, [])
                                                           Sym_add _ _ -> (case walk_on_scope syms (ident, (sym_attr_entity . sym_attr) sym) of
                                                                             Just e -> if (not ovwt) then (sym_tbl, last_id, [Symbol_redefinition errmsg])
                                                                                       else ((Scope_add (id, lv, anon_idents, (Sym_add sym syms)) scps), last_id, [])
                                                                               where
                                                                                 errmsg = "symbol table error, failed to register, " ++
                                                                                          "for detection of pre registered object with same identifier as " ++ ident
                                                                             Nothing -> ((Scope_add (id, lv, anon_idents, (Sym_add sym syms)) scps), last_id, [])
                                                                          )
                                                             where
                                                               walk_on_scope :: Symtbl_cluster -> (String, Syntree_node) -> Maybe Symtbl_node
                                                               walk_on_scope sym_cluster (ident, entity) =
                                                                 ras_trace "in walk_on_scope" (
                                                                 case sym_cluster of
                                                                   Sym_add sym syms -> if (((sym_ident sym) == ident) && (cmp_entity sym entity)) then Just sym
                                                                                       else walk_on_scope syms (ident, entity)
                                                                   Sym_empty -> Nothing
                                                                 )
                                                        )
  in
    let ((left, stbl), last_id) = sym_categorize' symtbl cat
    in
      let (stbl', last_id', err) =
            reg_sym (stbl, last_id + 1) (ident, Sym_entry {sym_key = last_id + 1, sym_ident = ident, sym_attr = Sym_attrib {sym_attr_geometry = (-1, -1), sym_attr_entity = entity}})
      in
        ((sym_update symtbl cat ((left, stbl'), last_id')), err)
  ) -}
sym_regist' :: Bool -> Symtbl -> Sym_category -> (String, Syntree_node) -> ((Symtbl, (Integer, Integer)), [Error_codes])
sym_regist' ovrid symtbl cat (ident, entity) =
  ras_trace "in sym_regist" (
  let reg_sym (sym_tbl, last_id) (ident, sym) =
        case sym_tbl of
          Scope_empty -> ((last_id + 1, ((Scope_add ((0, last_id + 1), 0, Symtbl_anon_ident {sym_anon_var = 1, sym_anon_record = 1}, (Sym_add sym Sym_empty)) Scope_empty), last_id + 1)), [])
          Scope_add (id_scp@(id_prev, id_crnt), lv, anon_idents, syms) scps ->
            (case syms of
                Sym_empty -> ((id_crnt, ((Scope_add (id_scp, lv, anon_idents, (Sym_add sym Sym_empty)) scps), last_id)), [])
                Sym_add _ _ -> (case walk_on_scope syms (ident, (sym_attr_entity . sym_attr) sym) of
                                  Just e -> if (not ovrid) then
                                              ((id_crnt, (sym_tbl, last_id)), [Symbol_redefinition errmsg])
                                            else 
                                              ((id_crnt, ((Scope_add (id_scp, lv, anon_idents, (Sym_add sym syms)) scps), last_id)), [])
                                    where
                                      errmsg = "symbol table error, failed to register, " ++ "for detection of pre registered object with same identifier as " ++ ident
                                  Nothing -> ((id_crnt, ((Scope_add (id_scp, lv, anon_idents, (Sym_add sym syms)) scps), last_id)), [])
                               )
                  where
                    walk_on_scope :: Symtbl_cluster -> (String, Syntree_node) -> Maybe Symtbl_node
                    walk_on_scope sym_cluster (ident, entity) =
                      ras_trace "in walk_on_scope" (
                      case sym_cluster of
                        Sym_add sym syms -> if (((sym_ident sym) == ident) && (cmp_entity sym entity)) then Just sym
                                            else walk_on_scope syms (ident, entity)
                        Sym_empty -> Nothing
                      )
            )
  in
    let ((left, stbl), last_id) = sym_categorize' symtbl cat
        new_key = last_id + 1
    in
      let ((id_scp, (stbl', last_id')), err) =
            reg_sym (stbl, new_key) (ident, Sym_entry {sym_key = new_key, sym_ident = ident, sym_attr = Sym_attrib {sym_attr_geometry = (-1, -1), sym_attr_entity = entity}})
      in
        ((sym_update symtbl cat ((left, stbl'), last_id'), (id_scp, new_key)), err)
  )

sym_subst :: [Subst] -> Symtbl -> Symtbl
sym_subst subst symtbl =
  ras_trace "in sym_subst" (
  let (stbl_decl, last_id) = sym_categorize' symtbl Sym_cat_decl
  in
    case (sym_scope_right stbl_decl) of
      Scope_empty -> symtbl
      Scope_add (id, lv, anon_id, syms) ss -> let stbl_decl_r' = Scope_add (id, lv, anon_id , subst_on_scope subst syms) ((sym_scope_right . fst) $ sym_categorize' symtbl' Sym_cat_decl)
                                              in
                                                sym_update symtbl Sym_cat_decl ((sym_scope_left stbl_decl, stbl_decl_r'), last_id)
        where
          symtbl' = sym_subst subst $ sym_update symtbl Sym_cat_decl ((sym_scope_left stbl_decl, ss), last_id)
          subst_on_scope :: [Subst] -> Symtbl_cluster -> Symtbl_cluster
          subst_on_scope subst syms =
            case syms of
              Sym_empty -> Sym_empty
              Sym_add sym@(Sym_entry {sym_attr = attr@(Sym_attrib {sym_attr_entity = entity})}) ss -> Sym_add sym{sym_attr = attr'} (subst_on_scope subst ss)
                where
                  attr' = attr{sym_attr_entity = (syn_node_subst subst entity)}
  )

sym_dump :: Symtbl -> Sym_category -> (Maybe [(String, [String])], Maybe [(String, [String])])
sym_dump symtbl cat =
  let traverse sym_tbl =
        case sym_tbl of
          Scope_empty -> []
          Scope_add (id, lv, anon_ident, syms) sym_tbl' -> ("(id, Lv)=(" ++ (show id) ++ " ," ++ (show lv) ++ ") : ", (walk syms)) : (traverse sym_tbl')
      walk syms =
        case syms of
          Sym_empty -> []
          Sym_add (Sym_entry {sym_key = key, sym_ident = ident, sym_attr = a}) syms' -> ("<" ++ "(" ++ (show key) ++ ", " ++ ident ++ ")" ++ ", " ++ (show_attr a) ++ ">") : (walk syms')
      show_attr (Sym_attrib {sym_attr_geometry = (row, col), sym_attr_entity = entity}) = show entity
  in
    let ldump = let ltbl = (sym_scope_left . fst) $ sym_categorize' symtbl cat
                in
                  case ltbl of
                    Nothing -> Nothing
                    Just ltbl' -> Just $ traverse ltbl'
        rdump = Just $ traverse ((sym_scope_right . fst) $ sym_categorize' symtbl cat)
    in
      (ldump, rdump)

print_symtbl :: Symtbl -> Sym_category -> IO ()
print_symtbl symtbl cat =
  let (ldump, rdump) = sym_dump symtbl cat
  in
    do
      putStr "syms_left: "
      case ldump of
        Nothing -> putStrLn "Nothing."
        Just ldump' -> do
          putStrLn ""
          Prelude.foldl (\r -> \s -> do
                            r' <- r
                            putStr " "
                            putStrLn (show s)
                        ) (return ()) ldump'
      
      putStr "syms_right:"
      case rdump of
        Nothing -> putStrLn "Nothing."
        Just rdump' -> do
          putStrLn ""
          Prelude.foldl (\r -> \s -> do
                            r' <- r
                            putStr " "
                            putStrLn (show s)
                        ) (return ()) rdump'

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

type Ty_env_bind = (String, Type)
type Ty_promote = (String, Type)
type Subst = (String, Type)
--type Prom = (String, Type)
type Prom = (String, (Maybe Type, Type))
data Ty_env =
  --Ty_env [(String, Type)]
  --Ty_env Ty_env_bind
  --Ty_env (Ty_env_bind, [Subst])
  --Ty_env [(Ty_env_bind, [Subst])]
  --Ty_env [(Ty_env_bind, ([Ty_promote], [Subst]))]
  --Ty_env [(Ty_env_bind, [Subst])]
  Ty_env [([Ty_env_bind], ([Prom], [Subst]))]
  deriving (Eq, Ord, Show)

{- ty_prom :: [Ty_promote] -> (String, Type) -> (String, Type)
ty_prom proms (var_id, ty) =
  case Prelude.lookup var_id proms of
    Just ty_p -> (var_id, Ty_prom ty ty_p)
    Nothing -> (var_id, ty) -}

ty_reveal :: Type -> Type
ty_reveal ty =
  case ty of
    Ty_prom ty0 ty' -> ty_reveal ty'
    Ty_ovride ty0 ty' -> ty_reveal ty'
    _ -> ty

ty_base :: Type -> Bool
ty_base ty =
  case ty of
    Ty_bool -> True
    Ty_string -> True
    Ty_int -> True
    _ -> False

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
          Ty_btm -> (case ty_1 of
                       Ty_btm -> True
                       _ -> False
                    )
          Ty_prom _ ty_2' -> is_subty ty_1 ty_2'
          Ty_ovride _ ty_2' -> is_subty ty_1 ty_2'
          _ -> False
  in
    if (is_subty ty_1 ty_2) then Just ty_2
    else
      if (is_subty ty_2 ty_1) then Just ty_1 else Nothing

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
            Ty_prom ty0 ty -> Ty_prom ty0 (subst1 subst ty)
            Ty_ovride ty0 ty -> Ty_ovride ty0 (subst1 subst ty)
            Ty_unknown -> ty_expr

ty_subst_env :: [Subst] -> Ty_env -> Ty_env
ty_subst_env subst env =
  case env of
    Ty_env [] -> env
    Ty_env (([], _):_) -> env
    Ty_env (((v_id, v_ty):bss, (p, s)):es) -> let v_ty' = ty_subst subst v_ty
                                              in
                                                {- case ty_subst_env subst (Ty_env ((bss, (p, s)):es)) of
                                                  Ty_env ((bss', (p', _)):es') -> Ty_env (((v_id, v_ty'):bss', (p', subst)):es')
                                                  Ty_env [] -> Ty_env [([(v_id, v_ty')], (p, subst))] -}
                                                case ty_subst_env subst (Ty_env ((bss, (p, s)):es)) of
                                                  Ty_env (([], _):_) -> Ty_env (([(v_id, v_ty')], (p, subst)):es)
                                                  Ty_env ((bss', (p', _)):es') -> Ty_env (((v_id, v_ty'):bss', (p', subst)):es')

ty_subst_env' :: [Subst] -> Ty_env -> Ty_env
ty_subst_env' subst env =
  case env of
    Ty_env [] -> env
    Ty_env (e:es) -> ty_subst_env subst (Ty_env (e:(e:es)))
  

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
  -- | Syn_fun_decl' (String, Integer) [Syntree_node] Syntree_node (Ty_env, Type)
  | Syn_fun_decl String [Syntree_node] Syntree_node Type
  -- | Syn_arg_decl String Type
  | Syn_arg_decl (String, Integer) Type
  | Syn_rec_decl String Type
  -- | Syn_var_decl String Type
  | Syn_var_decl (String, Integer) Type
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
  ty_reveal (case expr of
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
               _ -> Ty_unknown -- for Syn_scope, and Syn_node.
            )

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
  if (syn_node_typeof expr) == ty_prom then expr
  else
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
    Syn_cond_expr (expr_cond, (expr_true, expr_false)) ty -> Syn_cond_expr (expr_cond', (expr_true', expr_false')) (ty_subst subst ty)
      where
        expr_cond' = syn_node_subst subst expr_cond
        expr_true' = syn_node_subst subst expr_true
        expr_false' = case expr_false of
                        Nothing -> Nothing
                        Just f_expr -> Just $ syn_node_subst subst f_expr
    Syn_val val ty -> Syn_val val (ty_subst subst ty)
    Syn_var var_id ty -> Syn_var var_id (ty_subst subst ty)
    Syn_expr_asgn expr_l expr_r ty -> Syn_expr_asgn (syn_node_subst subst expr_l) (syn_node_subst subst expr_r) (ty_subst subst ty)
    Syn_expr_par expr_par ty -> Syn_expr_par (syn_node_subst subst expr_par) (ty_subst subst ty)   
    Syn_expr_call fun_id args ty -> Syn_expr_call fun_id (Prelude.map (syn_node_subst subst) args) (ty_subst subst ty)
    Syn_expr_una ope expr0 ty -> Syn_expr_una ope (syn_node_subst subst expr0) (ty_subst subst ty)
    Syn_expr_bin ope (expr1, expr2) ty -> Syn_expr_bin ope (syn_node_subst subst expr1, syn_node_subst subst expr2) (ty_subst subst ty)
    Syn_expr_seq exprs ty -> Syn_expr_seq (Prelude.map (syn_node_subst subst) exprs) (ty_subst subst ty)
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
  | Illegal_type_specified Tk_code
  | Illegal_operands Operation Syntree_node
  | Undefined_symbol String
  | Symbol_redefinition String
  | Illegal_symbol_declaration
  | Unknown_token_detected
  deriving (Eq, Ord, Show)


par_type_decl :: Symtbl -> [Tk_code] -> ExceptT Error_Excep IO (Either [Error_codes] Type, Symtbl, [Tk_code])
par_type_decl symtbl tokens =
  case tokens of
    Tk_typed_as:[] -> return (Left [Imcomplete_type_specifier], symtbl, [])
    Tk_typed_as:ts -> return (case ts of
                                Tk_bool:ts' -> (Right Ty_bool, symtbl, ts')
                                Tk_int:ts' -> (Right Ty_int, symtbl, ts')
                                t:ts' -> (Left [Illegal_type_specified t], symtbl, ts)
                             )
    _ -> throwE (Error_Excep Excep_assert_failed loc)
      where
        loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))


cons_var_decl :: Symtbl -> Syntree_node -> [Tk_code] -> ExceptT Error_Excep IO ((Maybe Syntree_node, Symtbl, [Tk_code]), [Error_codes])
cons_var_decl symtbl var tokens =
  case var of
    Syn_var var_id var_ty -> do
      r <- lift (case tokens of
                   Tk_typed_as:ts -> do
                     r_ty <- runExceptT $ par_type_decl symtbl tokens
                     return (case r_ty of
                               Left err -> Left err
                               Right (Right var_ty', symtbl', ts') -> Right ((Just (Syn_var_decl (var_id, -1) var_ty'), symtbl', ts'), [])
                               Right (Left err, symtbl', ts') -> Right ((Just (Syn_var_decl (var_id, -1) var_ty), symtbl', ts'), err)
                            )
                   _ -> return $ Right ((Just (Syn_var_decl (var_id, -1) var_ty), symtbl, tokens), [])
                )
      case r of
        Left err -> throwE err
        Right r' -> return r'
    _ -> throwE (Error_Excep Excep_assert_failed loc)
      where
        loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))


par_fun_decl :: Symtbl -> Syntree_node -> [Tk_code] -> ExceptT Error_Excep IO ((Syntree_node, Symtbl, [Tk_code]), [Error_codes])
par_fun_decl symtbl fun tokens =
  let par_fun_type symtbl tokens =
        case tokens of
          Tk_typed_as:ts -> do
            r_ty <- runExceptT $ par_type_decl symtbl tokens
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
                                    Right ((fun_ty', symtbl', tokens'), errs) -> Right ((Syn_fun_decl' fun_id [] fun_body (Ty_env binds, fun_ty'), symtbl', tokens'), errs)
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
                                                 errmsg = "missing closing R paren in parameter declarator of function declaration."
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
                                 r_arg <- runExceptT $ cons_var_decl symtbl arg ts
                                 return (case r_arg of
                                           Left err -> Left err
                                           Right ((Just (Syn_var_decl arg_id arg_ty), symtbl', ts'), errs) -> Right ((Just (Syn_arg_decl arg_id arg_ty), symtbl', ts'), errs)
                                           Right ((_, symtbl', ts'), errs) -> Left (Error_Excep Excep_assert_failed loc)
                                             where
                                               loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
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
      
      _ -> throwE (Error_Excep Excep_assert_failed loc)
        where
          loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))


type Redef_omits = [(String, Syntree_node)]

exam_redef :: ([Syntree_node], Redef_omits) -> ExceptT Error_Excep IO (([Syntree_node], Redef_omits), [Error_codes])
exam_redef (args, omits) =
  let chk_decls (as, omits) =
        case as of
          [] -> ((Right [], omits), [])
          [a] -> ((Right [snd a], omits), [])
          a:as' -> (case Prelude.lookup (fst a) omits of
                      Just _ -> (case chk_decls ((elide a ([], as')), omits) of
                                   ((Right as'', omits'), err) -> ((Right ((snd a):as''), omits'), err)
                                   ((Left as'', omits'), err) -> ((Left ((snd a):as''), omits'), err)
                                )
                      Nothing -> (case Prelude.lookup (fst a) as' of
                                    Nothing -> (case chk_decls (as', omits) of
                                                  ((Right as'', omits'), errs) -> ((Right ((snd a):as''), omits'), errs)
                                                  ((Left as'', omits'), errs) -> ((Left ((snd a):as''), omits'), errs)
                                               )
                                    Just _ -> (case chk_decls ((elide a ([], as')), a:omits) of
                                                 ((Right as'', omits'), errs) -> ((Left ((snd a):as''), omits'), ((Symbol_redefinition errmsg) : errs))
                                                 ((Left as'', omits'), errs) -> ((Left ((snd a):as''), omits'), ((Symbol_redefinition errmsg) : errs))
                                              )
                                      where
                                        errmsg = "Redefinition of " ++ (show $ fst a) ++ " in function arguments declaration."
                                 )
                   )
            where
              elide e decls = case decls of
                               (purged, []) -> purged
                               (purged, d:ds) | (fst d) == (fst e) -> elide e (purged, ds)
                               (purged, d:ds) -> elide e ((purged ++ [d]), ds)                                                      
  in
    do
      args' <- return $ Prelude.foldl (\as -> \a -> (do
                                                        as' <- as
                                                        case a of
                                                          (Syn_fun_decl' id _ _ _) -> Right (as' ++ [(id, a)])
                                                          (Syn_arg_decl (id, _) _) -> Right (as' ++ [(id, a)])
                                                          (Syn_var_decl (id, _) _) -> Right (as' ++ [(id, a)])
                                                          _ -> Left (Error_Excep Excep_assert_failed loc)
                                                            where
                                                              loc  = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                    )
                                      ) (Right []) args
      case args' of
        Left err_exc -> throwE err_exc
        Right args'' -> return (case chk_decls (args'', omits) of
                                  ((Right as'', omits'), errs_args) -> ((as'', omits'), errs_args)
                                  ((Left as'', omits'), errs_args) -> ((as'', omits'), errs_args)
                               )

parse_fun_body :: Symtbl -> ([Syntree_node], Redef_omits) -> [Tk_code] -> ExceptT Error_Excep IO (((Ty_env, ([Syntree_node], Redef_omits)), [Syntree_node]), Symtbl, [Tk_code], [Error_codes])
parse_fun_body symtbl (decls, omits) tokens@(Tk_R_bra:_) = return (((Ty_env [], (decls, omits)), []), symtbl, tokens, [])
parse_fun_body symtbl (decls, omits) tokens = do
  r <- lift (do
                r_body <- runExceptT $ cons_ptree symtbl tokens (True, True, True, True)
                case r_body of
                  Left err_exc -> return $ Left err_exc
                  Right body -> do
                    case body of
                      ((Nothing, symtbl', tokens'), err) -> return $ Right (((Ty_env [], (decls, omits)), []), symtbl', tokens', err)
                      
                      ((Just fun_decl@(Syn_fun_decl' fun_id args fun_body (env0, fun_ty)), symtbl', tokens'), err) -> do
                        r_decls <- runExceptT $ exam_redef ((decls ++ [fun_decl]), omits)
                        case r_decls of
                          Left err_exc -> return $ Left err_exc
                          Right ((decls', omits'), err_decl) ->
                            (case tokens' of
                               [] -> return $ Right (((env0, (decls', omits')), []), symtbl', [], (err ++ err_decl))
                               _ -> do
                                 r_body' <- runExceptT $ parse_fun_body symtbl' (decls', omits') tokens'
                                 return (case r_body' of
                                           Left err_exc -> Left err_exc
                                           Right (((env1, (decls'', omits'')), stmts), symtbl'', tokens'', err_cont) -> Right (((env', (decls'', omits'')), stmts), symtbl'', tokens'', err')
                                             where
                                               env' = ty_ovwt_env env0 env1
                                               err' =  err ++ err_decl ++ err_cont
                                        )
                            )
                      
                      ((Just var_decl@(Syn_var_decl _ _), symtbl', tokens'), err) -> do
                        r_decls <- runExceptT $ exam_redef ((decls ++ [var_decl]), omits)
                        case r_decls of
                          Left err_exc -> return $ Left err_exc
                          Right ((decls', omits'), err_decl) ->
                            (case tokens' of
                               [] -> return $ Right (((Ty_env [], (decls', omits')), []), symtbl', [], (err ++ err_decl ++ [Parse_error errmsg]))
                               Tk_smcl:ts' -> do
                                 r_body' <- runExceptT $ parse_fun_body symtbl' (decls', omits') ts'
                                 return (case r_body' of
                                           Left err_exc -> Left err_exc
                                           Right (((env1, (decls'', omits'')), stmts), symtbl'', tokens'', err_cont) -> Right (((env1, (decls'', omits'')), stmts), symtbl'', tokens'', err')
                                             where
                                               err' = err ++ err_decl ++ err_cont
                                        )
                               _ -> do
                                 r_body' <- runExceptT $ parse_fun_body symtbl' (decls', omits') tokens'
                                 return (case r_body' of
                                           Left err_exc -> Left err_exc
                                           Right (((env1, (decls'', omits'')), stmts), symtbl'', tokens'', err_cont) -> Right (((env1, (decls'', omits'')), stmts), symtbl'', tokens'', err')
                                             where
                                               err' = err ++ err_decl ++ ((Parse_error errmsg):err_cont)
                                        )
                            )
                            where
                              errmsg = "missing semicolon at the end of declaration."
                      
                      ((Just stmt, symtbl', tokens'), err) -> do
                        let (((env1, (decls', omits')), stmt1), symtbl1, tokens1, err1) = case stmt of
                              Syn_scope _ -> (((Ty_env [], (decls, omits)), stmt), symtbl', tokens', err)
                              Syn_cond_expr (_, (Syn_scope _, Nothing)) _ -> (((Ty_env [], (decls, omits)), stmt), symtbl', tokens', err)
                              Syn_cond_expr (_, (_, Just (Syn_scope _))) _ -> (((Ty_env [], (decls, omits)), stmt), symtbl', tokens', err)
                              _ -> (case tokens' of
                                      Tk_smcl:ts' -> (((Ty_env [], (decls, omits)), stmt), symtbl', ts', err)
                                      _ -> (((Ty_env [], (decls, omits)), stmt), symtbl', tokens', (err ++ [Parse_error errmsg]))
                                   )
                                where
                                  errmsg = "Missing semicolon at end of sentence."
                        
                        r_body' <- runExceptT $ parse_fun_body symtbl1 (decls', omits') tokens1
                        case r_body' of
                          Left err_exc -> return $ Left err_exc
                          Right (((env', (decls'', omits'')), stmts), symtbl'', tokens'', err_cont) -> return $ Right (((env', (decls'', omits'')), (stmt1:stmts)), symtbl'', tokens'', err')
                            where
                              err' = err1 ++ err_cont
                      
                      ((_, symtbl', tokens'), err) -> return $ Left (Error_Excep Excep_assert_failed loc)
                        where
                          loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
            )
  case r of
    Left err -> throwE err
    Right r' -> return r'

cons_fun_tree :: Symtbl -> Syntree_node -> [Tk_code] -> ExceptT Error_Excep IO ((Syntree_node, Symtbl, [Tk_code]), [Error_codes])
cons_fun_tree symtbl fun tokens =
  case fun of
    Syn_fun_decl' fun_id args fun_body (env, fun_ty) -> do
      r <- lift (do
                    r_decl <- runExceptT $ par_fun_decl symtbl fun tokens
                    case r_decl of
                      Left err -> return $ Left err
                      Right ((fun@(Syn_fun_decl' fun_id' args' fun_body' (env'@(Ty_env binds), fun_ty')), symtbl', tokens'), errs)
                        | fun_id' == fun_id -> do
                            case tokens' of
                              [] -> return $ Right ((Syn_fun_decl' fun_id' args' fun_body' (env', fun_ty'), symtbl', []), errs'')
                                where
                                  errmsg = "function has no body at its top level declaration."
                                  errs'' = errs ++ [Imcomplete_function_declaration errmsg]
                              _ -> (do
                                       r_args <- runExceptT $ exam_redef ((fun:args'), [])
                                       case r_args of
                                         Left err -> return $ Left err
                                         Right ((args0, omits), errs_args) -> do
                                           let args'' = Prelude.foldl (\as -> \a -> (case a of
                                                                                       Syn_arg_decl _ _ -> as ++ [a]
                                                                                       _ -> as
                                                                                    )
                                                                      ) [] args0
                                           let (ts', errs_parse) = case tokens' of
                                                                     Tk_L_bra:ts'' -> (ts'', [])
                                                                     _ -> (tokens', [Imcomplete_function_declaration errmsg])
                                                                       where
                                                                         errmsg = "missing beginning L brace in the declaration of function body."
                                                                         
                                           let ((symtbl'', reg_id), err_funreg) = sym_regist' False symtbl' Sym_cat_decl (fun_id', (Syn_fun_decl' fun_id' args'' fun_body' (env', fun_ty')))
                                           case sym_internalerr err_funreg of
                                             (e:es, _) -> return $ Left (Error_Excep Excep_assert_failed errmsg)
                                               where
                                                 errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                             _ -> do
                                               let lv_before = sym_crnt_level $ sym_scope_right (sym_categorize symtbl'' Sym_cat_decl)
                                               let (new_scope, errs_argreg) =
                                                     Prelude.foldl (\(stbl, errs) -> \arg@(Syn_arg_decl (id, _) _) ->
                                                                       case sym_internalerr errs of
                                                                         (e:es, _) -> (stbl, errs)
                                                                         _ -> (case sym_regist' False stbl Sym_cat_decl (id, arg) of
                                                                                 ((stbl', reg_id), err_reg) -> (stbl', (errs ++ err_reg))
                                                                              )
                                                                   ) (sym_enter_scope (Just symtbl'') Sym_cat_decl) args''
                                               case sym_internalerr errs_argreg of
                                                 (e:es, _) -> return $ Left (Error_Excep Excep_assert_failed errmsg)
                                                   where
                                                     errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                 _ -> do
                                                   let errs0 = errs ++ errs_args ++ errs_parse ++ err_funreg ++ errs_argreg
                                                   case fun_body' of
                                                     (Syn_scope ([], Syn_none)) -> do
                                                       r_body <- runExceptT $ parse_fun_body new_scope (args'', omits) ts'
                                                       case r_body of
                                                         Left err -> return $ Left err
                                                         Right (((Ty_env binds', (decls, _)), stmts), new_scope', ts'', errs_body) ->
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
                                                             case (case sym_leave_scope new_scope' Sym_cat_decl of
                                                                     (scp, err) -> (case sym_internalerr err of
                                                                                      (e:es, _) -> Left (Error_Excep Excep_assert_failed errmsg)
                                                                                        where
                                                                                          errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                                      _ -> Right (scp, err)
                                                                                   )
                                                                  ) of
                                                               Left err -> return $ Left err
                                                               Right (prev_scope, err_leave) ->
                                                                 if (sym_crnt_level (sym_scope_right $ sym_categorize prev_scope Sym_cat_decl)) /= lv_before then
                                                                   let loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                   in
                                                                     return $ Left (Error_Excep Excep_assert_failed loc)
                                                                 else
                                                                   do
                                                                     let ((prev_scope', _), err_funreg') =
                                                                           if (sym_crnt_level (sym_scope_right $ sym_categorize prev_scope Sym_cat_decl)) == 1 then
                                                                             sym_regist' False prev_scope Sym_cat_func (fun_id', fun'')
                                                                           else
                                                                             ((prev_scope, (-1, -1)), [])
                                                                     case sym_internalerr err_funreg' of
                                                                       (e:es, _) -> return $ Left (Error_Excep Excep_assert_failed errmsg)
                                                                         where
                                                                           errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                       _ -> do
                                                                         let errs1 = errs0 ++ errs_body ++ err_leave ++ err_funreg'  
                                                                         case ts'' of
                                                                           Tk_R_bra:tokens'' -> return $ Right ((fun'', prev_scope', tokens''), errs1)
                                                                           _ -> return $ Right ((fun'', prev_scope', ts''), (errs1 ++ [Imcomplete_function_declaration errmsg]))
                                                                             where
                                                                               errmsg = "Missing R brace to close up declaration of function body."
                                                     
                                                     _ -> return $ Left (Error_Excep Excep_assert_failed loc)
                                                       where
                                                         loc  = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                   )
                      
                      _ -> return $ Left (Error_Excep Excep_assert_failed loc)
                        where
                          loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                )
      case r of
        Left err -> throwE err
        Right r' -> return r'
    
    _ -> throwE (Error_Excep Excep_assert_failed loc)
      where
        loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))

cons_ptree :: Symtbl -> [Tk_code] -> (Bool, Bool, Bool, Bool) -> ExceptT Error_Excep IO ((Maybe Syntree_node, Symtbl, [Tk_code]), [Error_codes])
cons_ptree symtbl tokens (fun_declp, var_declp, comp_parsp, par_contp) =
  let cat_err err expr = do
        expr' <- expr
        return (case expr' of
                  Left err_exc -> Left err_exc
                  Right ((expr0, symtbl', tokens'), err') -> Right ((expr0, symtbl', tokens'), (err ++ err'))
               )
      
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
          Nothing -> return ((Just subexpr1, symtbl, tokens'), [])
          Just ope' | ope' == Ope_asgn -> do
                        r <- lift (do
                                      rhs <- runExceptT $ cons_ptree symtbl tokens' (False, False, False, True)
                                      case rhs of
                                        Left err_exc -> return $ Left err_exc
                                        --Right ((Just expr_r, symtbl', tokens''), err) -> return $ Right ((Just (Syn_expr_asgn subexpr1 expr_r Ty_abs), symtbl', tokens''), err)
                                        Right ((Just expr_r, symtbl', tokens''), err) -> do
                                          r_inf <- runExceptT $ ty_inf symtbl' (Syn_expr_asgn subexpr1 expr_r Ty_abs)
                                          case r_inf of
                                            Left ((env, expr_asgn), symtbl'', err_inf) -> return $ Right ((Just expr_asgn, symtbl'', tokens''), err ++ err_inf)
                                            Right ((env, expr_asgn), symtbl'', err_inf) -> return $ Right ((Just expr_asgn, symtbl'', tokens''), err ++ err_inf)
                                        Right ((Nothing, symtbl', tokens''), err) -> return $ Right ((Just subexpr1, symtbl', tokens''), err)
                                  )
                        case r of
                          Left err_exc -> throwE err_exc
                          Right r' -> return r'
          Just ope' | is_bin_op ope' -> do
                        r <- lift (do
                                      r2 <- runExceptT $ cons_ptree symtbl tokens' (False, False, False, True)
                                      case r2 of
                                        Left err_exc -> return $ Left err_exc
                                        Right ((Just subexpr2, symtbl', tokens''), err) ->
                                          (case combine subexpr1 ope' subexpr2 of
                                             Left exc -> return $ Left exc
                                             Right expr' -> return $ Right ((Just expr', symtbl', tokens''), err)
                                          )
                                        Right ((Nothing, symtbl', tokens''), err) -> return $ Right ((Just subexpr1, symtbl', tokens''), err)
                                  )
                        case r of
                          Left err -> throwE err
                          Right r' -> return r'
          _ -> throwE  (Error_Excep Excep_assert_failed loc)
            where
              loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
        
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
              Syn_expr_bin op2 (expr21, expr22) ty2 -> if is_gte_op op op2 then
                                                         case combine expr1 op expr21 of
                                                           Right expr21' -> Right $ Syn_expr_bin op2 (expr21', expr22) Ty_abs
                                                           Left exc -> Left exc
                                                       else
                                                         Right $ Syn_expr_bin op (expr1, expr2) Ty_abs
              _ -> Left (Error_Excep Excep_assert_failed loc)
                where
                  loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
      
      par_fun_call symtbl fun_app tokens = do
        r <- lift (case fun_app of
                     Syn_expr_call fun_id app_args fun_ty -> do
                       case tokens of
                         [] -> return $ Right ((fun_app, symtbl, []), err)
                           where
                             err = [Parse_error "missing closing right parenthesis."]
                         Tk_R_par:ts -> return $ Right ((fun_app, symtbl, tokens), [])
                         _ -> do
                           let (r_lk, err_lok) = sym_lkup_fun_decl symtbl fun_id
                           case r_lk of
                             Just ((Sym_attrib {sym_attr_entity = Syn_fun_decl' ident params (Syn_scope (decls, body)) (env, ty)}, h), symtbl')
                               | ident == fun_id -> (case sym_internalerr err_lok of
                                                       (e:es, err') -> return $ Left (Error_Excep Excep_assert_failed loc)
                                                         where
                                                           loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                       ([], err') -> cat_err err_lok $ par_args symtbl' (Just params) tokens
                                                    )
                             Just (_, symtbl') -> return $ Left (Error_Excep Excep_assert_failed loc)
                               where
                                 loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                             Nothing -> cat_err err' $ par_args symtbl Nothing tokens
                               where
                                 errmsg = "Function " ++ (show fun_id) ++ " is undefined."
                                 err' = err_lok ++ [Undefined_symbol errmsg]
                             
                             where
                               par_args :: Symtbl -> (Maybe [Syntree_node]) -> [Tk_code] -> IO (Either Error_Excep ((Syntree_node, Symtbl, [Tk_code]), [Error_codes]))
                               par_args symtbl params tokens = do
                                 let err_args = [Parse_error "too many arguments in function calling. excessive ones are omitted."]
                                 r_a <- runExceptT $ cons_ptree symtbl tokens (False, False, False, True)
                                 case r_a of
                                   Left err_exc -> return $ Left err_exc
                                   Right ((Nothing, symtbl', tokens'), err) -> return $ Right (((Syn_expr_call fun_id [] fun_ty), symtbl', tokens'), err)
                                   
                                   Right ((Just arg, symtbl', tokens'), err) ->
                                     case params of
                                       Just [] -> do
                                         r_as <- omits_args symtbl' tokens'
                                         case r_as of
                                           Left err_exc -> return $ Left err_exc
                                           Right (symtbl'', tokens'') -> return $ Right (((Syn_expr_call fun_id [] fun_ty), symtbl'', tokens''), err ++ err_args)
                                       Just (p:ps) -> (case ps of
                                                         [] -> (case tokens' of
                                                                  Tk_comma:ts' -> do
                                                                    r_as <- omits_args symtbl' tokens'
                                                                    case r_as of
                                                                      Left err_exc -> return $ Left err_exc
                                                                      Right (symtbl'', tokens'') -> return $ Right (((Syn_expr_call fun_id [arg] fun_ty), symtbl'', tokens''), err')
                                                                        where
                                                                          err' = err ++ err_args
                                                                  _ -> return $ Right (((Syn_expr_call fun_id [arg] fun_ty), symtbl', tokens'), err)
                                                               )
                                                         _ -> (case tokens' of
                                                                 Tk_comma:ts' -> cont symtbl' (Just ps) tokens'
                                                                 _ -> do
                                                                   r_as <- omits_args symtbl' tokens'
                                                                   case r_as of
                                                                     Left err_exc -> return $ Left err_exc
                                                                     Right (symtbl'', tokens'') -> return $ Right (((Syn_expr_call fun_id [arg] fun_ty), symtbl'', tokens''), err')
                                                                       where
                                                                         err' = err ++ err_args
                                                              )
                                                      )
                                       
                                       Nothing -> cont symtbl' Nothing tokens'
                                       
                                     where
                                       omits_args :: Symtbl -> [Tk_code] -> IO (Either Error_Excep (Symtbl, [Tk_code]))
                                       omits_args symtbl tokens =
                                         case tokens of
                                           [] -> return $ Right (symtbl, [])
                                           _ -> do
                                             r_a <- runExceptT $ cons_ptree symtbl tokens (False, False, False, True)
                                             case r_a of
                                               Left err_exc -> return $ Left err_exc
                                               Right ((Nothing, symtbl', tokens'), _) -> return $ Right (symtbl', tokens')
                                               Right ((Just _, symtbl', Tk_comma:ts'), _) -> omits_args symtbl' ts'
                                               Right ((Just _, symtbl', tokens'), _) -> return $ Right (symtbl', tokens')
                                       
                                       cont symtbl params tokens = do
                                         r_as <- par_args symtbl params tokens
                                         return $ case r_as of
                                           Left err_exc -> Left err_exc
                                           Right (((Syn_expr_call fun_id' args' fun_ty'), symtbl'', tokens''), err')
                                             | fun_id' == fun_id -> Right (((Syn_expr_call fun_id' (arg:args') fun_ty'), symtbl'', tokens''), (err ++ err'))
                                           _ -> Left (Error_Excep Excep_assert_failed loc)
                                             where
                                               loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                   
                                     {- case tokens' of
                                       Tk_comma:ts' -> do
                                         case params of
                                           Just (p:ps) -> cont symtbl' (Just ps) tokens'
                                           {- Just _ -> return $ Right (((Syn_expr_call fun_id [] fun_ty), symtbl', tokens'), err')
                                             where
                                               err' = err ++ [Parse_error "too many arguments in function calling"] -}
                                           Just _ -> do
                                             r_as <- omits_args symtbl' tokens'
                                             case r_as of
                                               Left err_exc -> return $ Left err_exc
                                               Right (symtbl'', tokens'') -> return $ Right (((Syn_expr_call fun_id [] fun_ty), symtbl'', tokens''), err')
                                               where
                                                 err' = err ++ [Parse_error "too many arguments in function calling. excessive ones are omitted."]
                                                 
                                                 omits_args :: Symtbl -> [Tk_code] -> IO (Either Error_Excep (Symtbl, [Tk_code]))
                                                 omits_args symtbl tokens =
                                                   case tokens of
                                                     [] -> return $ Right (symtbl, [])
                                                     _ -> do
                                                       r_a <- runExceptT $ cons_ptree symtbl tokens (False, False, False, True)
                                                       case r_a of
                                                         Left err_exc -> return $ Left err_exc
                                                         Right ((Nothing, symtbl', tokens'), _) -> return $ Right (symtbl', tokens')
                                                         Right ((Just _, symtbl', Tk_comma:ts'), _) -> omits_args symtbl' ts'
                                                         Right ((Just _, symtbl', tokens'), _) -> return $ Right (symtbl', tokens')
                                           
                                           Nothing -> cont symtbl' Nothing tokens'
                                           where
                                             cont symtbl params tokens = do
                                               r_as <- par_args symtbl params tokens
                                               return $ case r_as of
                                                          Left err_exc -> Left err_exc
                                                          Right (((Syn_expr_call fun_id' args' fun_ty'), symtbl'', tokens''), err')
                                                            | fun_id' == fun_id -> Right (((Syn_expr_call fun_id' (arg:args') fun_ty'), symtbl'', tokens''), (err ++ err'))
                                                          _ -> Left (Error_Excep Excep_assert_failed loc)
                                                            where
                                                              loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                               
                                       _ -> return $ Right (((Syn_expr_call fun_id [arg] fun_ty), symtbl', tokens'), err) -}
                                   
                                   Right ((Nothing, symtbl', tokens'), err) -> return $ Right ((fun_app, symtbl', tokens'), err)
                     _ -> return $ Left (Error_Excep Excep_assert_failed loc)
                       where
                         loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                  )
        case r of
          Left err -> throwE err
          Right r' -> return r'
      
      insane symtbl tokens errs =
        case tokens of
          [] -> return ((Nothing, symtbl, tokens), errs)
          t:ts -> do
            r <- lift (do
                          r' <- runExceptT $ cons_ptree symtbl ts (True, True, True, True)
                          case r' of
                            Left err_exc -> return $ Left err_exc
                            Right ((Just _, symtbl', ts'), err) -> cat_err errs (return r')
                            Right ((Nothing, symtbl', ts'), err) -> (do
                                                                        r'' <- runExceptT $ insane symtbl' ts' (errs ++ err)
                                                                        case r'' of
                                                                          Left err_exc -> return $ Left err_exc
                                                                          Right _ -> return r''
                                                                    )
                      )
            case r of
              Left err_exc -> throwE err_exc
              Right r' -> return r'
  in
    let cont_par symtbl subexpr tokens = do
          if par_contp then (
            do
              r <- lift (do
                            r_cont <- runExceptT $ cons_expr symtbl subexpr tokens
                            case r_cont of
                              Left err_exc -> return $ Left err_exc
                              Right ((Nothing, symtbl', tokens'), err) -> return $ Right ((Nothing, symtbl', tokens'), err)
                              --Right ((Just expr', symtbl', tokens'), err) -> Right ((Just expr', symtbl', tokens'), err)
                              Right ((Just expr', symtbl', tokens'), err) -> do
                                r_cur <- runExceptT $ ty_curve symtbl' expr'
                                return (case r_cur of
                                          Left [Internal_error errmsg] -> Left (Error_Excep Excep_assert_failed errmsg)
                                          Right (expr'', symtbl'') -> Right ((Just expr'', symtbl'', tokens'), err)
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
        Tk_smcl:ts -> return ((Just Syn_none, symtbl, ts), [])
        
        Tk_L_bra:ts ->
          if comp_parsp then do
            case ts of
              --[] -> return ((Just (Syn_expr_seq [Syn_none] Ty_btm), symtbl, []), [Parse_error errmsg])
              [] -> return ((Just (Syn_scope ([], Syn_none)), symtbl, []), [Parse_error errmsg_R_bra])
              Tk_R_bra:ts' -> return ((Just (Syn_scope ([], Syn_none)), symtbl, ts'), [])
              _ -> do
                r <- lift (do
                              r_comp <- runExceptT $ cons_ptree symtbl ts (True, True, True, True)
                              case r_comp of
                                Left err_exc -> return $ Left err_exc
                                Right ((Nothing, symtbl', ts'), err) -> return (case ts of
                                                                                  Tk_R_bra:ts'' -> Right ((([], []), symtbl', ts'), err)
                                                                                  _ -> Right ((([], []), symtbl', ts'), (err ++ [Parse_error errmsg_R_bra]))
                                                                               )
                                Right ((Just stmt, symtbl', ts'), err) ->
                                  (case is_decl stmt of
                                     Left err_exc -> return $ Left err_exc
                                     Right declp -> do
                                       needs_delim <- tail_comp stmt
                                       case needs_delim of
                                         Left err_exc -> return $ Left err_exc
                                         Right smclp -> do
                                           r_comp' <- (if declp then par_comp (([stmt], ([], smclp)), []) symtbl' ts'
                                                       else par_comp (([], ([], smclp)), [stmt]) symtbl' ts'
                                                      )
                                           case r_comp' of
                                             Left err_exc -> return $ Left err_exc
                                             Right ((body, symtbl'', ts''), err') -> cat_err err $ return (case ts'' of
                                                                                                             Tk_R_bra:tokens' -> Right ((body, symtbl'', tokens'), err')
                                                                                                             _ -> Right ((body, symtbl'', ts''), err'')
                                                                                                               where
                                                                                                                 err'' = err' ++ [Parse_error errmsg_R_bra]
                                                                                                          )
                                  )
                                  where
                                    is_decl :: Syntree_node -> Either Error_Excep Bool
                                    is_decl stmt =
                                      case stmt of
                                        Syn_tydef_decl _ _ -> Right True
                                        Syn_fun_decl' _ _ _ _ -> Right True
                                        Syn_rec_decl _ _ -> Right True
                                        Syn_var_decl _ _ -> Right True
                                        Syn_arg_decl _ _ -> Left (Error_Excep Excep_assert_failed loc)
                                          where
                                            loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                        _ -> Right False  -- including the case of Syn_none
                                    
                                    tail_comp :: Syntree_node -> IO (Either Error_Excep Bool)
                                    tail_comp stmt =
                                      return (case stmt of
                                                --Syn_scope ([Syntree_node], Syntree_node)
                                                Syn_scope _ -> Right True
                                                --Syn_tydef_decl String Type
                                                Syn_tydef_decl _ _ -> Right False
                                                --Syn_fun_decl' String [Syntree_node] Syntree_node (Ty_env, Type)
                                                Syn_fun_decl' _ _ _ _ -> Right True
                                                --Syn_arg_decl String Type
                                                Syn_arg_decl _ _ -> Left (Error_Excep Excep_assert_failed loc)
                                                  where
                                                    loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                --Syn_rec_decl String Type
                                                Syn_rec_decl _ _ -> Right False
                                                --Syn_var_decl String Type
                                                Syn_var_decl _ _ -> Right False
                                                --Syn_cond_expr (Syntree_node, (Syntree_node, Maybe Syntree_node)) Type
                                                Syn_cond_expr (_, (Syn_scope _, Nothing)) _ -> Right True
                                                Syn_cond_expr (_, (_, Just (Syn_scope _))) _ -> Right True
                                                Syn_cond_expr _ _ -> Right False
                                                --Syn_val Val Type
                                                Syn_val _ _ -> Right False
                                                --Syn_var String Type
                                                Syn_var _ _ -> Right False
                                                --Syn_expr_asgn Syntree_node Syntree_node Type
                                                Syn_expr_asgn _ _ _ -> Right False
                                                --Syn_expr_par Syntree_node Type
                                                Syn_expr_par _ _ -> Right False
                                                --Syn_expr_call String [Syntree_node] Type
                                                Syn_expr_call _ _ _ -> Right False
                                                --Syn_expr_una Operation Syntree_node Type
                                                Syn_expr_una _ _ _ -> Right False
                                                --Syn_expr_bin Operation (Syntree_node, Syntree_node) Type
                                                Syn_expr_bin _ _ _ -> Right False
                                                --Syn_expr_seq [Syntree_node] Type
                                                Syn_expr_seq _ _ -> Right False
                                                --Syn_none
                                                Syn_none -> Right False
                                             )
                                    
                                    par_comp :: (([Syntree_node], (Redef_omits, Bool)), [Syntree_node]) -> Symtbl -> [Tk_code]
                                             -> IO (Either Error_Excep ((([Syntree_node], [Syntree_node]), Symtbl, [Tk_code]), [Error_codes]))
                                    par_comp ((decls, (decl_omits, delim_omits)), stmts) symtbl tokens =
                                      case tokens of
                                        [] -> return $ Right (((decls, stmts), symtbl, []), (if delim_omits then [] else [Parse_error errmsg]))
                                        Tk_R_bra:ts -> return $ Right (((decls, stmts), symtbl, tokens), (if delim_omits then [] else [Parse_error errmsg]))
                                        Tk_smcl:Tk_R_bra:ts -> return $ Right (((decls, stmts), symtbl, Tk_R_bra:ts), [])
                                        _ -> do
                                          (tokens', err_delim) <- return (case tokens of
                                                                            Tk_smcl:ts -> (ts, [])
                                                                            _ -> (tokens, if delim_omits then [] else [Parse_error errmsg])
                                                                         )
                                          r_stmt <- runExceptT $ cons_ptree symtbl tokens' (True, True, True, True)
                                          case r_stmt of
                                            Left err_exc -> return $ Left err_exc
                                            Right ((Nothing, symtbl', ts'), err) -> cat_err err_delim (return $ Right (((decls, stmts), symtbl', ts'), err))
                                            Right ((Just Syn_none, symtbl', ts'), err) -> return $ Left (Error_Excep Excep_assert_failed loc)
                                              where
                                                loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                            Right ((Just stmt, symtbl', ts'), err) -> do
                                              needs_delim <- tail_comp stmt
                                              case needs_delim of
                                                Left err_exc -> return $ Left err_exc
                                                Right smclp ->
                                                  (case is_decl stmt of
                                                     Left err_exc -> return $ Left err_exc
                                                     Right declp | declp -> do
                                                                     r_chk <- runExceptT $ exam_redef ((decls ++ [stmt]), decl_omits)
                                                                     case r_chk of
                                                                       Left err_exc -> return $ Left err_exc
                                                                       Right ((decls'', decl_omits'), err_redef) -> do
                                                                         cat_err (err_delim ++ err ++ err_redef) $ par_comp ((decls'', (decl_omits', smclp)), stmts) symtbl' ts'
                                                     _ -> cat_err (err_delim ++ err) $ par_comp ((decls, (decl_omits, smclp)), (stmts ++ [stmt])) symtbl' ts'
                                                  )
                                    errmsg = "missing semicolon at the end of statement."
                          )
                case r of
                  Left err_exc -> throwE err_exc
                  Right (((decls, stmts), symtbl', tokens'), err) -> return ((Just (Syn_scope (decls, body')), symtbl', tokens'), err)
                    where
                      body' = (case stmts of
                                 [] -> Syn_none
                                 _ -> Syn_expr_seq stmts (syn_node_typeof (head $ reverse stmts))
                              )
          else
            return ((Nothing, symtbl, ts), [Parse_error errmsg_L_bra])
          where
            errmsg_L_bra = "expected expression."
            errmsg_R_bra = "missing closing R brace of compound statement."
        
        Tk_L_par:ts -> do
          r <- lift $ runExceptT $ cons_ptree symtbl ts (False, False, False, True)
          case r of
            Left err -> throwE err
            Right ((Just par_expr, symtbl', (Tk_R_par:ts')), err) -> do
              r' <- lift (do
                             r_par <- cat_err err (runExceptT $ cont_par symtbl' (Syn_expr_par par_expr (syn_node_typeof par_expr)) ts')
                             return (case r_par of
                                       Left err_exc -> Left err_exc
                                       Right (r_cont, err') -> Right (r_cont, err')
                                    )
                         )
              case r' of
                Left err_exc -> throwE err_exc
                Right r'' -> return r''
            Right ((Just par_expr, symtbl', ts'), err) -> do
              r' <- lift (do
                             let errmsg = "Missing R-paren of the expression."
                             let err' = err ++ [Ill_formed_expression errmsg]
                             r_cont <- cat_err err' (runExceptT $ cont_par symtbl' (Syn_expr_par par_expr (syn_node_typeof par_expr)) ts')
                             return (case r_cont of
                                       Left err_exc -> Left err_exc
                                       Right ((Just par_expr', symtbl'', ts''), err'') -> Right ((Just par_expr', symtbl'', ts''), err'')
                                       Right ((_, symtbl'', ts''), err'') -> Right ((Nothing, symtbl', ts'), err'')
                                    )
                         )
              case r' of
                Left err_exc -> throwE err_exc
                Right r'' -> return r''
            Right ((_, symtbl',ts'), err) -> return ((Nothing, symtbl', ts'), err)
        
        Tk_if:ts -> do
          r <- lift (do
                        r_cond <- runExceptT $ cons_ptree symtbl ts (False, False, False, True)
                        case r_cond of
                          Left err_exc -> return $ Left err_exc
                          Right ((Just cond_expr, symtbl', tokens'), err_c) ->
                            case tokens' of
                              Tk_then:ts' -> do
                                --r_true <- cat_err err_c (runExceptT $ cons_ptree symtbl' ts' (False, False, True))
                                r_true <- (case ts' of
                                             Tk_L_bra:ts'' -> cat_err err_c (runExceptT $ cons_ptree symtbl' ts' (False, False, True, True))
                                             _ -> do
                                               r_true' <- cat_err err_c (runExceptT $ cons_ptree symtbl' ts' (False, False, False, True))
                                               case r_true' of
                                                 Left err_exc -> return $ Left err_exc
                                                 Right ((t_expr, symtbl'', Tk_smcl:Tk_else:ts''), err_ct) -> return $ Right ((t_expr, symtbl'', (Tk_else:ts'')), err_ct)
                                                 Right ((t_expr, symtbl'', Tk_smcl:ts''), err_ct) -> return $ Right ((t_expr, symtbl'', (Tk_smcl:ts'')), err_ct)
                                                 Right ((t_expr, symtbl'', ts''), err_ct) -> return $ Right ((t_expr, symtbl'', ts''), err_ct')
                                                   where
                                                     errmsg = "missing semicolon at end of sentence."
                                                     err_ct' = err_ct ++ [Parse_error errmsg]
                                          )
                                case r_true of
                                  Left err_exc -> return $ Left err_exc
                                  Right ((Just true_expr, symtbl'', (Tk_else:ts'')), err_ct) -> par_else_clause (true_expr, err_ct) symtbl'' ts''
                                  Right ((Just true_expr, symtbl'', tokens''), err_ct) ->
                                    return $ Right ((Just (Syn_cond_expr (cond_expr, (true_expr, Nothing)) Ty_abs), symtbl'', tokens''), err_ct)
                                  Right ((_, symtbl'', tokens''), err) -> return $ Right ((Nothing, symtbl'', tokens''), err)
                              _ -> return $ Right ((Nothing, symtbl', tokens'), err')
                                where
                                  errmsg = "Expected \"then\", in conditional expression."
                                  err' = err_c ++ [Parse_error errmsg]
                            where
                              par_else_clause (true_expr, err_ct) symtbl tokens = do
                                --r_false <- cat_err err_ct (runExceptT $ cons_ptree symtbl tokens (False, False, True))
                                r_false <- (case tokens of
                                              Tk_L_bra:ts' -> cat_err err_ct (runExceptT $ cons_ptree symtbl tokens (False, False, True, True))
                                              _ -> do
                                                f_false' <- cat_err err_ct (runExceptT $ cons_ptree symtbl tokens (False, False, False, True))
                                                case f_false' of
                                                  Left err_exc -> return $ Left err_exc
                                                  Right ((f_exr, symtbl', Tk_smcl:tokens'), err_ctf) -> return $ Right ((f_exr, symtbl', Tk_smcl:tokens'), err_ctf)
                                                  Right ((f_exr, symtbl', tokens'), err_ctf) -> return $ Right ((f_exr, symtbl', tokens'), err_ctf)
                                                    where
                                                      errmsg = "missing semicolo nat end of sentence."
                                                      err_ctf' = err_ctf ++ [Parse_error errmsg]
                                           )
                                return (case r_false of
                                          Left err_exc -> Left err_exc
                                          Right ((Just false_expr, symtbl', tokens'), err) ->
                                            Right ((Just (Syn_cond_expr (cond_expr, (true_expr, Just false_expr)) Ty_abs), symtbl', tokens'), err)
                                          Right ((_, symtbl'', tokens'), err) -> Right ((Nothing, symtbl'', tokens'), err)
                                       )
                          Right ((_, symtbl', tokens'), err) -> return $ Right ((Nothing, symtbl', tokens'), err)
                    )
          case r of
            Left err -> throwE err
            Right r' -> return r'
        
        Tk_decre:ts -> (case ts of
                          --(Tk_ident ident):ts' -> cont_par symtbl (Syn_expr_una Ope_decre (Syn_var ident Ty_abs) Ty_abs) ts'
                           (Tk_ident ident):ts' -> do
                             let expr = (Syn_expr_una Ope_decre (Syn_var ident Ty_abs) Ty_abs)
                             r <- lift $ do
                               r_cur <- runExceptT $ ty_curve symtbl expr
                               case r_cur of
                                 --Left err_cur -> return $ Right ((Just expr, symtbl, ts'), err_cur)
                                 Left [Internal_error errmsg] -> return $ Left (Error_Excep Excep_assert_failed errmsg)
                                 --Right (expr', symtbl') -> runExceptT $ cont_par symtbl' expr' ts'
                                 Right (expr', symtbl') -> do
                                   r_inf <- runExceptT $ ty_inf symtbl' expr'
                                   case r_inf of
                                     Left ((env, expr''), symtbl'', err_inf) -> cat_err err_inf (runExceptT $ cont_par symtbl'' expr'' ts')
                                     Right ((env, expr''), symtbl'', err_inf) -> cat_err err_inf (runExceptT $ cont_par symtbl'' expr'' ts')
                             case r of
                               Left r' -> throwE r'
                               Right r' -> return r'
                             
                           _ -> return ((Nothing, symtbl, ts), err)
                             where
                               errmsg = "Expression must be assignable."
                               err = [Ill_formed_expression errmsg]
                       )
        Tk_incre:ts -> (case ts of
                          --(Tk_ident ident):ts' -> cont_par symtbl (Syn_expr_una Ope_incre (Syn_var ident Ty_abs) Ty_abs) ts'
                          (Tk_ident ident):ts' -> do
                            let expr = Syn_expr_una Ope_incre (Syn_var ident Ty_abs) Ty_abs
                            r <- lift $ do
                              r_cur <- runExceptT $ ty_curve symtbl expr
                              case r_cur of
                                --Left err_cur -> return $ Right ((Just expr, symtbl, ts), err_cur)
                                Left [Internal_error errmsg] -> return $ Left (Error_Excep Excep_assert_failed errmsg)
                                --Right (expr', symtbl') -> runExceptT $ cont_par symtbl' expr' ts'
                                Right (expr', symtbl') -> do
                                  r_inf <- runExceptT $ ty_inf symtbl' expr'
                                  case r_inf of
                                    Left ((env, expr''), symtbl'', err_inf) -> cat_err err_inf (runExceptT $ cont_par symtbl'' expr'' ts')
                                    Right ((env, expr''), symtbl'', err_inf) -> cat_err err_inf (runExceptT $ cont_par symtbl'' expr'' ts')
                                  
                            case r of
                              Left r' -> throwE r'
                              Right r' -> return r'
                          _ -> return ((Nothing, symtbl, ts), err)
                            where
                              errmsg = "Expression must be assignable."
                              err = [Ill_formed_expression errmsg]
                       )
                       
        Tk_shaft:ts -> do
          r <- lift (do
                        r0 <- runExceptT $ cons_ptree symtbl ts (False, False, False, False)
                        case r0 of
                          Left err_exc -> return $ Left err_exc
                          Right ((Nothing, symtbl0, ts'), err0) -> return r0
                          Right ((Just expr0, symtbl0, ts'), err0) -> do
                            r_cur <- runExceptT $ ty_curve symtbl0 expr0
                            case r_cur of
                              Left [Internal_error errmsg] -> return $ Left (Error_Excep Excep_assert_failed errmsg)
                              {- Right (expr0', symtbl0') -> do
                                r1 <- cat_err err0 (runExceptT $ cont_par symtbl0' (Syn_expr_una Ope_neg expr0' Ty_abs) ts')
                                case r1 of
                                  Left err_exc -> return r1
                                  Right ((expr1, symtbl'', ts''), err) -> return r1 -}
                              Right (expr0', symtbl0') -> do
                                r_inf <- runExceptT $ ty_inf symtbl0' (Syn_expr_una Ope_neg expr0' Ty_abs)
                                case r_inf of
                                  Left ((env, expr1), symtbl'', err_inf) -> cat_err (err0 ++ err_inf) (runExceptT $ cont_par symtbl'' expr1 ts')
                                  Right ((env, expr1), symtbl'', err_inf) -> cat_err (err0 ++ err_inf) (runExceptT $ cont_par symtbl'' expr1 ts')
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
                              r_decl <- runExceptT $ cons_fun_tree symtbl fun ts'
                              case r_decl of
                                Left err -> return $ Left err
                                Right ((fun'@(Syn_fun_decl' fun_id' args' fun_body' (env', fun_ty')), symtbl', tokens'), errs)
                                  | fun_id' == fun_id -> return $ Right ((Just fun', symtbl', tokens'), errs)
                                Right ((_, symtbl', tokens'), errs) -> return $ Left (Error_Excep Excep_assert_failed loc)
                                  where
                                    loc = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                          )
                case r of
                  Left err -> throwE err
                  Right r' -> return r'
              
              _ -> return ((Nothing, symtbl, ts), [err])
                where
                  errmsg = "Invalid function declaration."
                  err = Imcomplete_function_declaration errmsg
            
            else let errmsg = "Illegal function declaration."
                     err = Parse_error errmsg
                 in
                   return ((Nothing, symtbl, ts), [err])
            
        Tk_var:ts -> if var_declp then
                       do
                         r <- lift (case ts of
                                      (Tk_ident ident):ts' -> do
                                        let var = Syn_var ident Ty_abs
                                        r_v <- runExceptT $ cons_var_decl symtbl var ts'
                                        case r_v of
                                          Left err -> return $ Left err
                                          Right ((Just (var_decl@(Syn_var_decl (var_id, _) var_ty)), symtbl', tokens'), errs) -> do
                                            r_cur <- runExceptT $ ty_curve symtbl' var_decl
                                            case r_cur of
                                              Left [Internal_error errmsg] -> return $ Left (Error_Excep Excep_assert_failed errmsg)
                                              Right (var_decl', symtbl'_cur) -> return $ Right ((Just var_decl', symtbl'', tokens'), (errs ++ err_symreg))
                                                where
                                                  ((symtbl'', reg_id), err_symreg) = sym_regist' False symtbl'_cur Sym_cat_decl (var_id, var_decl')
                                          
                                          Right ((_, symtbl', tokens'), errs) -> return $ Right ((Nothing, symtbl', tokens'), errs)
                                      _ -> return $ Right ((Nothing, symtbl, ts), [err])
                                        where
                                          errmsg = ""
                                          err = Imcomplete_variable_declaration errmsg
                                   )
                         case r of
                           Left err ->throwE err
                           Right r' -> return r'
                     else let errmsg = "Illegal variable declaration."
                              err = Parse_error errmsg
                          in
                            return ((Nothing, symtbl, ts), [err])
        
        (Tk_ident ident):ts -> do
          r <- lift (do
                        case ts of
                          Tk_L_par:ts' -> do
                            let fun_app = Syn_expr_call ident [] Ty_abs
                            r_call <- runExceptT $ par_fun_call symtbl fun_app ts'
                            case r_call of
                              Left err_exc -> return $ Left err_exc
                              Right (((fun_app'@(Syn_expr_call fun_id app_args app_ty)), symtbl', tokens'), err) -> do
                                case tokens' of
                                  Tk_R_par:ts'' -> cat_err err (runExceptT $ cont_par symtbl' fun_app' ts'')
                                  _ -> cat_err err' (runExceptT $ cont_par symtbl' fun_app' (skip tokens'))
                                    where
                                      errmsg = "Missing closing R paren in function calling."
                                      err' = err ++ [Ill_formed_expression errmsg]
                                      skip tokens =
                                        case tokens of
                                          [] -> []
                                          t:ts -> if cmp follows t then ts else skip ts
                                            where
                                              follows = [Tk_R_par]
                                              cmp cands t =
                                                case cands of
                                                  c:cs | c == t -> True
                                                  _ -> False
                              
                              _ -> return $ Left (Error_Excep Excep_assert_failed errmsg)
                                where
                                  errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                          
                          _ -> do
                            let var = Syn_var ident Ty_abs
                            case sym_lkup_var_decl symtbl ident of
                              (Just ((Sym_attrib {sym_attr_entity = v}, (h@(Sym_cat_decl, _))), symtbl'), err) ->
                                (case sym_internalerr err of
                                   (e:es, err') -> return $ Left (Error_Excep Excep_assert_failed errmsg)
                                     where
                                       errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                   ([], err') -> (case v of
                                                    Syn_var_decl ident' v_ty | (fst ident') == ident -> do
                                                                                 let var' = Syn_var ident v_ty
                                                                                 r_cur <- cur_tv var' (ident', (symtbl', h))
                                                                                 case r_cur of
                                                                                   Left err_cur -> return $ Left (Error_Excep Excep_assert_failed errmsg)
                                                                                     where
                                                                                       errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                                   Right (var'', (symtbl'', _), err_cur) -> cat_err err'' (runExceptT $ cont_par symtbl'' var'' ts)
                                                                                     where
                                                                                       err'' = err' ++ err_cur
                                                    _ -> do
                                                      r_cur <- cur_tv var ((ident, -1), (symtbl', h))
                                                      case r_cur of
                                                        Left err_cur -> return $ Left (Error_Excep Excep_assert_failed errmsg)
                                                          where
                                                            errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                        Right (var', (symtbl'', _), err_cur) -> cat_err err'' (runExceptT $ cont_par symtbl'' var' ts)
                                                          where
                                                            errmsg = ident ++ " hasn't been declared as variable"
                                                            err'' = err' ++ err_cur ++ [Type_constraint_mismatched errmsg]
                                                            
                                                 )
                                     where
                                       cur_tv :: Syntree_node -> ((String, Integer), (Symtbl, (Sym_category, (Sym_tbl, Sym_tbl)))) ->
                                                 IO (Either [Error_Excep] (Syntree_node, (Symtbl, Sym_handle), [Error_codes]))
                                       cur_tv var ((id_reg, key_reg), (symtbl, h)) =
                                         case var of
                                           Syn_var ident v_ty | ident == id_reg -> do
                                                                  r_cur <- runExceptT $ ty_curve symtbl var
                                                                  case r_cur of
                                                                    Left [Internal_error errmsg] -> return $ Left [Error_Excep Excep_assert_failed errmsg]
                                                                    Right (var'@(Syn_var ident' v_ty'), symtbl')
                                                                      | ident' == ident ->
                                                                        if v_ty' == v_ty then return $ Right (var', (symtbl', h), [])
                                                                        else
                                                                          if key_reg > 0 then
                                                                            do
                                                                              let attr_mod = Sym_attrib {sym_attr_geometry = (-1, -1), sym_attr_entity = Syn_var_decl (ident, key_reg) v_ty'}
                                                                              let r_mod = sym_modify (symtbl', h) ident attr_mod
                                                                              return $ case r_mod of
                                                                                (Just ((a, h'), symtbl''), err_mod)
                                                                                  | a == attr_mod -> (case sym_internalerr err_mod of
                                                                                                        (e:es, err_mod') -> Left [Error_Excep Excep_assert_failed errmsg]
                                                                                                          where
                                                                                                            errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                                                        ([], err_mod') -> Right (var', (symtbl'', h'), err_mod')
                                                                                                     )
                                                                                (_, err_mod) -> Left (case sym_internalerr err_mod of
                                                                                                        (e:es, err_mod') -> [Error_Excep Excep_assert_failed errmsg]
                                                                                                          where
                                                                                                            errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                                                        ([], err_mod') -> [Error_Excep Excep_assert_failed errmsg]
                                                                                                          where
                                                                                                            errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                                                     )
                                                                          else do
                                                                            ((symtbl'', reg_id), err_reg) <-
                                                                              return $ sym_regist' False symtbl' Sym_cat_decl (ident, Syn_var_decl (ident, -1) v_ty')
                                                                            case sym_internalerr err_reg of
                                                                              (e:es, err_reg') -> return $ Left [Error_Excep Excep_assert_failed errmsg]
                                                                                where
                                                                                  errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                              --([], err_reg') -> cat_err err'' (runExceptT $ cont_par symtbl'' var' ts)
                                                                              ([], err_reg') -> return $ Right (var', (symtbl'', h), err_reg')
                                                                    Right _ -> return $ Left [Error_Excep Excep_assert_failed errmsg]
                                                                      where
                                                                        errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                           _ -> return $ Left [Error_Excep Excep_assert_failed errmsg]
                                             where
                                               errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                )
                              (Just _, err) -> (case sym_internalerr err of
                                                  (es_fatal, es_others) -> return $ Left (Error_Excep Excep_assert_failed errmsg)
                                                    where
                                                      errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                               )
                              
                              (Nothing, err) -> do
                                case sym_internalerr err of
                                  (e:es, err') -> return $ Left (Error_Excep Excep_assert_failed errmsg)
                                    where
                                      errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                  ([], err') -> do
                                    r_cur <- runExceptT $ ty_curve symtbl var
                                    case r_cur of
                                      Left [Internal_error errmsg] -> return $ Left (Error_Excep Excep_assert_failed errmsg)
                                      Right (var'@(Syn_var ident' v_ty'), symtbl')
                                        | ident' == ident -> do
                                            ((symtbl'', reg_id), err_reg) <- return $ sym_regist' False symtbl' Sym_cat_decl (ident, Syn_var_decl (ident, -1) v_ty')
                                            case sym_internalerr err_reg of
                                              (e:es, err_reg') -> return $ Left (Error_Excep Excep_assert_failed errmsg)
                                                where
                                                  errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                              ([], err_reg') -> cat_err err'' (runExceptT $ cont_par symtbl'' var' ts)
                                                where
                                                  err'' = err' ++ err_reg'
                                      _ -> return $ Left (Error_Excep Excep_assert_failed errmsg)
                                        where
                                          errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                    )
          case r of
            Left err -> throwE err
            Right r' -> return r'
        
        {- _ -> return ((Nothing, symtbl, tokens), [err])
          where
            errmsg = "Encounted unknown token."
            err = Parse_error errmsg -}
        _ -> insane symtbl tokens []


recons_src :: Symtbl -> Syntree_node -> String
recons_src symtbl prg =
  let prn_val v = case v of
                    Val_str s -> s
                    Val_bool b -> show b
                    Val_int i -> show i
      prn_op op = case op of
                    Ope_asgn -> ":="
                    Ope_decre -> "--"
                    Ope_incre -> "++"
                    Ope_neg -> "-"
                    Ope_add -> "+"
                    Ope_sub -> "-"
                    Ope_mul -> "*"
                    Ope_div -> "/"
      prn_ty ty = case ty of
                    Ty_top -> "TOP"
                    Ty_bool -> "bool"
                    Ty_string -> "string"
                    Ty_int -> "int"
                    Ty_var tv_id -> "tvar@" ++ tv_id
                    Ty_pair (ty1, ty2) -> "(" ++ (prn_ty ty1) ++ ", " ++ (prn_ty ty2) ++ ")"
                    Ty_fun args ty -> let str_args = Prelude.foldl (\s -> \a -> (s ++ (prn_ty a) ++ " -> ")) "" args
                                      in
                                        case str_args of
                                          "" -> prn_ty ty
                                          _ -> "(" ++ (prn_ty ty) ++ ")"
                    Ty_abs -> "ABS"
                    Ty_btm -> "BTM"
                    Ty_prom ty_prev ty_prom -> prn_ty ty_prom
                    Ty_ovride ty_prev ty_ovrd -> prn_ty ty_ovrd
                    Ty_unknown -> "UNKNWN"
  in
    case prg of
      --Syn_scope ([Syntree_node], Syntree_node)
      Syn_scope (decls, body) -> "{" ++ (Prelude.foldl (\s -> \d -> (s ++ (recons_src symtbl d) ++ "; ")) "" decls) ++ (recons_src symtbl body) ++ "}"
      --Syn_tydef_decl String Type
      Syn_tydef_decl def_id ty -> ""
      --Syn_fun_decl' String [Syntree_node] Syntree_node (Ty_env, Type)
      Syn_fun_decl' fun_id fun_args fun_body (_, fun_ty) -> "fun " ++ fun_id ++
        " (" ++ (Prelude.foldl (\s -> \a -> (s ++ (recons_src symtbl a) ++ "; ")) "" fun_args) ++ ")" ++ " as " ++ (prn_ty fun_ty) ++ " " ++ (recons_src symtbl fun_body)
      --Syn_arg_decl String Type
      Syn_arg_decl (arg_id, key) ty -> arg_id ++ " as " ++ (prn_ty ty')
        where
          ty' = case sym_find symtbl Sym_cat_decl (Nothing, key) of
                  ((Nothing, symbol'), err) -> ty
                    where
                      errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                      err' = err ++ [Internal_error errmsg]
                  ((Just (ident_reg, Sym_attrib {sym_attr_entity = Syn_var_decl (arg_id', key') ty_reg}), symtbl'), err) -> ty_reg
                    where
                      err' = if (ident_reg == arg_id) && (arg_id' == arg_id) && (key == key') then err
                             else let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                  in err ++ [Internal_error errmsg]
      --Syn_rec_decl String Type
      Syn_rec_decl rec_id ty -> ""
      --Syn_var_decl String Type
      Syn_var_decl (var_id, key) ty -> "var " ++ var_id ++ " as " ++ (prn_ty ty')
        where
          ty' = case sym_find symtbl Sym_cat_decl (Nothing, key) of
                  ((Nothing, symbol'), err) -> ty
                    where
                      errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                      err' = err ++ [Internal_error errmsg]
                  ((Just (ident_reg, Sym_attrib {sym_attr_entity = Syn_var_decl (var_id', key') ty_reg}), symtbl'), err) -> ty_reg
                    where
                      err' = if (ident_reg == var_id) && (var_id' == var_id) && (key == key') then err
                             else let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                  in err ++ [Internal_error errmsg]
      --Syn_cond_expr (Syntree_node, (Syntree_node, Maybe Syntree_node)) Type
      Syn_cond_expr (cond_expr, (true_expr, false_expr)) ty -> "if " ++ "(" ++ (recons_src symtbl cond_expr) ++ ")" ++ " then " ++  (recons_src symtbl true_expr) ++
        (case false_expr of
           Nothing -> ""
           Just f_clause -> " else " ++ (recons_src symtbl f_clause)
        )
      --Syn_val Val Type
      Syn_val val ty -> prn_val val
      --Syn_var String Type
      Syn_var v_id ty -> v_id
      --Syn_expr_asgn Syntree_node Syntree_node Type
      Syn_expr_asgn l_expr r_expr ty -> (recons_src symtbl l_expr) ++ (" " ++ (prn_op Ope_asgn) ++ " ") ++ (recons_src symtbl r_expr)
      --Syn_expr_par Syntree_node Type
      Syn_expr_par expr ty -> "(" ++ (recons_src symtbl expr) ++ ")"
      --Syn_expr_call String [Syntree_node] Type
      Syn_expr_call fun_id app_args ty -> fun_id ++ "(" ++
        Prelude.foldl (\s -> \a -> (case s of
                                      "" -> recons_src symtbl a
                                      _ -> s ++ ", " ++ (recons_src symtbl a)
                                   )
                      ) "" app_args
        ++ ")"
      --Syn_expr_una Operation Syntree_node Type
      Syn_expr_una op_una expr0 ty -> (prn_op op_una) ++ (recons_src symtbl expr0)
      --Syn_expr_bin Operation (Syntree_node, Syntree_node) Type
      Syn_expr_bin op_bin (expr1, expr2) ty -> "(" ++ (recons_src symtbl expr1) ++ (" " ++ (prn_op op_bin) ++ " ") ++ (recons_src symtbl expr2) ++ ")"
      --Syn_expr_seq [Syntree_node] Type
      Syn_expr_seq stmts ty -> Prelude.foldl (\str -> \s -> (str ++ (recons_src symtbl s) ++ "; ")) "" stmts
      --Syn_none
      Syn_none -> ""


type Fresh_tvar = (Type, Integer)

fresh_tvar_initial :: Fresh_tvar
fresh_tvar_initial = (Ty_var $ "t_" ++ (show 0), 0)

succ_flesh_tvar :: Fresh_tvar -> Fresh_tvar
succ_flesh_tvar prev =
  (Ty_var $ "t_" ++ show (last_id + 1), last_id + 1)
  where
    last_id = (snd prev)

ty_curve :: Symtbl -> Syntree_node -> ExceptT [Error_codes] IO (Syntree_node, Symtbl)
ty_curve symtbl expr = do
  case expr of
    Syn_arg_decl arg_id Ty_abs -> return (Syn_arg_decl arg_id (fst tvar_arg), symtbl')
      where
        symtbl' = sym_adjust_tvar symtbl $ succ_flesh_tvar (fresh_tvar symtbl)
        tvar_arg = fresh_tvar symtbl'
    Syn_var var_id Ty_abs -> return (Syn_var var_id (fst tvar_var), symtbl')
      where
        symtbl' = sym_adjust_tvar symtbl $ succ_flesh_tvar (fresh_tvar symtbl)
        tvar_var = fresh_tvar symtbl'
    
    Syn_expr_par expr' ty_par -> do
      r <- lift (do
                    r' <- runExceptT $ ty_curve symtbl expr'
                    return $ case r' of
                               Left err -> r'
                               Right (expr'', symtbl') -> Right (case ty_par of
                                                                   Ty_abs -> (Syn_expr_par expr'' (syn_retrieve_typeof expr''), symtbl')
                                                                   _ -> (Syn_expr_par expr'' ty_par, symtbl')
                                                                )
                )
      case r of
        Left err -> throwE err
        Right r' -> return r'
    
    Syn_expr_una ope_una expr' ty_una -> do
      r <- lift (do
                    r' <- runExceptT $ ty_curve symtbl expr'
                    return $ case r' of
                      Left err -> r'
                      Right (expr'', symtbl') -> Right (case ty_una of
                                                           Ty_abs -> (Syn_expr_una ope_una expr'' (fst tvar_una), symtbl'')
                                                             where
                                                               symtbl'' = sym_adjust_tvar symtbl' $ succ_flesh_tvar (fresh_tvar symtbl')
                                                               tvar_una = fresh_tvar symtbl''
                                                           _ -> (Syn_expr_una ope_una expr'' ty_una, symtbl')
                                                       )
                )
      case r of
        Left err -> throwE err
        Right r' -> return r'
    
    Syn_expr_bin ope_bin (expr1, expr2) ty_bin -> do
      r <- lift (do
                    r1 <- runExceptT $ ty_curve symtbl expr1
                    case r1 of
                      Left err -> return r1
                      Right (expr1', symtbl1) -> do
                        r2 <- runExceptT $ ty_curve symtbl1 expr2
                        return $ case r2 of
                                   Left err -> r2
                                   Right (expr2', symtbl2) -> Right (case ty_bin of
                                                                       Ty_abs -> (Syn_expr_bin ope_bin (expr1', expr2') (fst tvar_bin), symtbl')
                                                                         where
                                                                           symtbl' = sym_adjust_tvar symtbl2 $ succ_flesh_tvar (fresh_tvar symtbl2)
                                                                           tvar_bin = fresh_tvar symtbl'
                                                                       _ -> (Syn_expr_bin ope_bin (expr1', expr2') ty_bin, symtbl2)
                                                                    )
                )
      case r of
        Left err -> throwE err
        Right r' -> return r'
    
    Syn_expr_call fun_id args ty_call -> do
      r <- lift (do
                    r_args <- case args of
                                [] -> return $ Right ([], symtbl)
                                _ -> runExceptT $ curve_args symtbl' args
                                  where
                                    symtbl' = sym_adjust_tvar symtbl $ succ_flesh_tvar (fresh_tvar symtbl)
                    return r_args
                )
      case r of
        Left err -> throwE err
        Right (args', symtbl') -> return $ case ty_call of
                                             Ty_abs -> (Syn_expr_call fun_id args' (fst tvar_call), symtbl'')
                                               where
                                                 symtbl'' = sym_adjust_tvar symtbl' $ succ_flesh_tvar (fresh_tvar symtbl')
                                                 tvar_call = fresh_tvar symtbl''
                                             _ -> (Syn_expr_call fun_id args' ty_call, symtbl')
        where
          curve_args = curve_decls
    
    Syn_cond_expr (cond_expr, (expr_true, expr_false)) ty_cond -> do
      r <- lift (do
                    r_cond <- runExceptT $ ty_curve symtbl cond_expr
                    case r_cond of
                      Left err -> return r_cond
                      Right (cond_expr', symtbl_c) -> do
                        r_true <- runExceptT $ ty_curve symtbl_c expr_true
                        case r_true of
                          Left err -> return r_true
                          Right (expr_true', symtbl_ct) -> do
                            r_false <- (case expr_false of
                                          Nothing -> return $ Right (Nothing, symtbl_ct)
                                          Just f_expr -> do
                                            r_false' <- runExceptT $ ty_curve symtbl_ct f_expr
                                            case r_false' of
                                              Left err -> return $ Left err
                                              Right (f_expr', symtbl_ctf) -> return $ Right (Just f_expr', symtbl_ctf)
                                       )
                            case r_false of
                              Left err -> return $ Left err
                              Right (expr_false', symtbl') -> return $ Right (case ty_cond of
                                                                                Ty_abs -> (Syn_cond_expr (cond_expr', (expr_true', expr_false')) (fst tvar_cond), symtbl'')
                                                                                  where
                                                                                    symtbl'' = sym_adjust_tvar symtbl' $ succ_flesh_tvar (fresh_tvar symtbl')
                                                                                    tvar_cond = fresh_tvar symtbl''
                                                                                _ -> (Syn_cond_expr (cond_expr', (expr_true', expr_false')) ty_cond, symtbl')
                                                                             )
                )
      case r of
        Left err -> throwE err
        Right r' -> return r'
    
    Syn_fun_decl' fun_id args fun_body (_, ty_fun) -> do
      r <- lift (do
                      r_args <- case args of
                                  [] -> return $ Right ([], symtbl)
                                  _ -> runExceptT $ curve_decls symtbl args
                      case r_args of
                        Left err -> return $ Left err
                        Right (args', symtbl_a) -> do
                          r_body <- runExceptT $ ty_curve symtbl_a fun_body
                          case r_body of
                            Left err -> return r_body
                            Right (fun_body', symtbl') -> return $ Right (Syn_fun_decl fun_id args' fun_body' ty_fun', symtbl'')
                              where
                                (ty_fun', symtbl'') = case ty_fun of
                                                        --Ty_abs -> curve_funty (args', ty_fun) prev_tvar''
                                                        Ty_abs -> (case curve_funty (args', ty_fun) (succ_flesh_tvar $ fresh_tvar symtbl') of
                                                                     (ty_fun'', last) -> (ty_fun'', sym_adjust_tvar symtbl' last)
                                                                  )
                                                        _ -> (ty_fun, symtbl')
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
    
    Syn_var_decl var_id Ty_abs -> return (Syn_var_decl var_id (fst tvar_var), symtbl')
      where
        symtbl' = sym_adjust_tvar symtbl $ succ_flesh_tvar (fresh_tvar symtbl)
        tvar_var = fresh_tvar symtbl'
    
    Syn_expr_seq exprs seq_ty -> do
      r <- lift (do
                    r_exprs <- case exprs of
                                 [] -> return $ Right ([], symtbl)
                                 e:es -> do
                                   r_e <- runExceptT $ ty_curve symtbl e
                                   case r_e of
                                     Left err -> return $ Left err
                                     Right (e', symtbl') -> (do
                                                                r_es <- runExceptT $ curve_seqs symtbl' es
                                                                case r_es of
                                                                  Left err -> return r_es
                                                                  Right (es', symtbl'') -> return $ Right ((e':es'), symtbl'')
                                                            )
                                       where
                                         curve_seqs = curve_decls
                    case r_exprs of
                      Left err -> return $ Left err
                      Right (exprs', symtbl') -> return $ Right (case seq_ty of
                                                                   Ty_abs -> (Syn_expr_seq exprs' seq_ty', symtbl'')
                                                                     where
                                                                       (seq_ty', symtbl'')  = case exprs' of
                                                                                                [] -> (fst (fresh_tvar symtbl''), symtbl'')
                                                                                                  where
                                                                                                    symtbl'' = sym_adjust_tvar symtbl' $ succ_flesh_tvar (fresh_tvar symtbl')
                                                                                                _ -> (syn_retrieve_typeof (Syn_expr_seq exprs' seq_ty), symtbl')
                                                                   _ -> (Syn_expr_seq exprs' seq_ty, symtbl')
                                                                )
                )
      case r of
        Left err -> throwE err
        Right r'-> return r'
    
    Syn_scope (decls, body) -> do
      r <- lift (do
                    r_decls <- runExceptT $ curve_decls symtbl decls
                    case r_decls of
                      Left err -> return $ Left err
                      Right (decls', symtbl') -> do
                        r_body <- runExceptT $ ty_curve symtbl' body
                        case r_body of
                          Left err -> return r_body
                          Right (body', symtbl'') -> return $ Right (Syn_scope (decls', body'), symtbl'')
                )
      case r of
        Left err -> throwE err
        Right r' -> return r'
    
    Syn_expr_asgn expr_l expr_r ty_asgn -> do
      r <- lift (do
                    r_l <- runExceptT $ ty_curve symtbl expr_l
                    case r_l of
                      Left err -> return r_l
                      Right (expr_l', symtbl') -> do
                        r_r <- runExceptT $ ty_curve symtbl' expr_r
                        case r_r of
                          Left err -> return r_r
                          Right (expr_r', symtbl'') -> return $ Right (Syn_expr_asgn expr_l' expr_r' ty_asgn', symtbl'')
                          where
                            ty_asgn' = case ty_asgn of
                                         Ty_abs -> syn_retrieve_typeof expr_l'
                                         _ -> ty_asgn
                )
      case r of
        Left err -> throwE err
        Right r' -> return r'
    
    --Syn_val _ Ty_abs -> throwE (Error_Excep Excep_assert_failed loc)
    Syn_val _ Ty_abs -> throwE [Internal_error errmsg]
      where
        errmsg  = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
    
    _ -> return (expr, symtbl) -- including the case of  Syn_tydef_decl, Syn_rec_decl, and Syn_none.
  
  where
    curve_decls :: Symtbl -> [Syntree_node] -> ExceptT [Error_codes] IO ([Syntree_node], Symtbl)
    curve_decls symtbl decls = do
      r <- lift (do
                    case decls of
                      [] -> return $ Right ([], symtbl)
                      d:ds -> do
                        r' <- runExceptT $ ty_curve symtbl d
                        case r' of
                          Left err -> return (Left err)
                          Right (d', symtbl') -> do
                            r'' <- runExceptT $ curve_decls symtbl' ds
                            return $ case r'' of
                                       Left err -> r''
                                       Right (ds', symtbl'') -> Right (d':ds', symtbl'')
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

{- ty_overlap_env1 :: Ty_env -> Ty_env -> ((Ty_env, Ty_env), [Equation])
ty_overlap_env1 env1 env2 =
  case env1 of
    Ty_env [] -> ((env1, env2), [])
    Ty_env ((bs1, s1):bss1) -> case env2 of
                                 Ty_env [] -> ((env1, env2), [])
                                 Ty_env ((bs2, s2):bss2) -> let overlaps = Set.intersection (Set.fromList $ Prelude.map fst bs1) (Set.fromList $ Prelude.map fst bs2)
                                   in
                                                              case Set.toList overlaps of
                                                                [] -> ((env1, env2), [])
                                                                vs -> (case enum_equs vs (bs1, bs2) of
                                                                         ((bs1', bs2'), equs) -> ((Ty_env ((bs1', s1):bss1), Ty_env ((bs2', s2):bss2)), equs)
                                                                      )
                                   where
                                     enum_equs :: [String] -> ([(String, Type)], [(String, Type)]) -> (([(String, Type)], [(String, Type)]), [Equation])
                                     enum_equs overlaps (bs1, bs2) =
                                       case overlaps of
                                         [] -> ((bs1, bs2), [])
                                         (v:vs) -> (case (Prelude.lookup v bs1, Prelude.lookup v bs2) of
                                                      (Just ty1, Just ty2) -> (case ty_lcs ty1 ty2 of
                                                                                 Just lcs -> go_on v (ty1, ty2, lcs)
                                                                                 Nothing -> (case ty_lcs ty2 ty1 of
                                                                                               Just lcs' -> go_on v (ty1, ty2, lcs')
                                                                                               Nothing -> (case enum_equs vs (bs1, bs2) of
                                                                                                             ((bs1', bs2'), equs) -> ((bs1', bs2'), (ty1, ty2):equs)
                                                                                                          )
                                                                                            )
                                                                              )
                                                        where
                                                          promote :: Type -> Type -> Type
                                                          promote ty_orig ty_prom = if ty_orig == ty_prom then ty_orig else (Ty_prom ty_orig ty_prom)
                                                          
                                                          go_on :: String -> (Type, Type, Type) -> (([(String, Type)], [(String, Type)]), [Equation])
                                                          go_on var_id (ty1, ty2, ty_lcs) =
                                                            let s_bs1' = Set.toList $ Set.difference (Set.fromList bs1) (Set.fromList [(var_id, ty1)])
                                                                s_bs2' = Set.toList $ Set.difference (Set.fromList bs2) (Set.fromList [(var_id, ty2)])
                                                            in
                                                              enum_equs vs (((var_id, promote ty1 ty_lcs):s_bs1'), ((var_id, promote ty2 ty_lcs):s_bs2'))
                                                      _ -> enum_equs vs (bs1, bs2)
                                                   ) -}

ty_equ_envs :: Ty_env -> Ty_env -> ((Ty_env, Ty_env), [Equation])
ty_equ_envs env1 env2 =
  case env1 of
    Ty_env [] -> ((env1, env2), [])
    Ty_env ((bs1, s1):bss1) -> case env2 of
                                 Ty_env [] -> ((env1, env2), [])
                                 Ty_env ((bs2, s2):bss2) -> let overlaps = Set.intersection (Set.fromList $ Prelude.map fst bs1) (Set.fromList $ Prelude.map fst bs2)
                                                            in
                                                              case Set.toList overlaps of
                                                                [] -> ((env1, env2), [])
                                                                vs -> (case enum_equs vs (bs1, bs2) of
                                                                         ((bs1', bs2'), equs) -> ((Ty_env ((bs1', s1):bss1), Ty_env ((bs2', s2):bss2)), equs)
                                                                      )
                                   where
                                     enum_equs :: [String] -> ([(String, Type)], [(String, Type)]) -> (([(String, Type)], [(String, Type)]), [Equation])
                                     enum_equs overlaps (bs1, bs2) =
                                       case overlaps of
                                         [] -> ((bs1, bs2), [])
                                         (v:vs) -> (case (Prelude.lookup v bs1, Prelude.lookup v bs2) of
                                                      (Just ty1, Just ty2) -> (case enum_equs vs (bs1, bs2) of
                                                                                  ((bs1', bs2'), equs) -> ((bs1', bs2'), (ty1, ty2):equs)
                                                                              )
                                                      _ -> enum_equs vs (bs1, bs2)
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

{- ty_merge_env :: Ty_env -> Ty_env -> Maybe Ty_env
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
        chk_and_merge env1_binds env2_binds = Prelude.foldl (\e1_bs -> \(v_id, ty) -> do
                                                                e1_bs' <- e1_bs
                                                                e1_bs'' <- (case Prelude.lookup v_id e1_bs' of
                                                                               Nothing -> Just e1_bs'
                                                                               Just ty_e1 | ty_e1 == ty -> Just e1_bs'
                                                                               _ -> Nothing
                                                                           )
                                                                return $ e1_bs'' ++ [(v_id, ty)]
                                                            ) (Just env1_binds) env2_binds -}
ty_merge_env :: Ty_env -> Ty_env -> Maybe Ty_env
ty_merge_env env_1 env_2 =
  case env_2 of
    Ty_env [] -> Just env_1
    Ty_env ((bs_2, _):bss_2) -> (case env_1 of
                                   Ty_env [] -> Just env_2
                                   Ty_env ((bs_1, _):bss_1) -> (case chk_and_merge bs_1 bs_2 of
                                                                  Just bs_m -> Just (Ty_env [(bs_m, ([], []))])
                                                                  Nothing -> Nothing
                                                               )
                                )
      where
        chk_and_merge env1_binds env2_binds = Prelude.foldl (\e1_bs -> \(v_id, ty) -> do
                                                                e1_bs' <- e1_bs
                                                                e1_bs'' <- (case Prelude.lookup v_id e1_bs' of
                                                                               Nothing -> Just e1_bs'
                                                                               Just ty_e1 | ty_e1 == ty -> Just e1_bs'
                                                                               _ -> Nothing
                                                                           )
                                                                return $ e1_bs'' ++ [(v_id, ty)]
                                                            ) (Just env1_binds) env2_binds

ty_chk_var_decl :: Symtbl -> (String, Type) -> ExceptT [Error_codes] IO (((String, Type), (Maybe Type, Maybe Type)), Symtbl, [Error_codes])
ty_chk_var_decl symtbl (v_id, v_ty) =
  case sym_lkup_var_decl symtbl v_id of
    (_, err_lok) | (fst . sym_internalerr) err_lok /= [] -> throwE ((Internal_error errmsg):err_lok)
      where
        errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
    (Nothing, err_lok) -> let ((symtbl', reg_id), err_reg) = sym_regist' False symtbl Sym_cat_decl (v_id, Syn_var_decl (v_id, -1) v_ty)
                          in
                            case (fst . sym_internalerr) err_reg of
                              [] -> return (((v_id, v_ty), (Nothing, Nothing)), symtbl', (err_reg ++ err_lok))
                              _ -> throwE ((Internal_error errmsg):(err_reg ++ err_lok))
                                where
                                  errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
    
    (Just ((Sym_attrib {sym_attr_entity = v_attr}, h), symtbl'), err_lok) ->
      (case v_attr of
          Syn_var_decl (v_id', v_key) v_ty_decl | v_id' == v_id ->
                                                  if (ty_reveal v_ty_decl) == v_ty then return (((v_id, v_ty), (Nothing, Just v_ty)), symtbl', err_lok)
                                                  else do
                                                    let v_ty_decl' = ty_reveal v_ty_decl
                                                    case ty_lcs v_ty v_ty_decl' of
                                                      Just _ -> return (((v_id, v_ty), (Nothing, Just v_ty_decl')), symtbl', err_lok)
                                                      Nothing -> (case ty_lcs v_ty_decl' v_ty of
                                                                    Just lcs ->
                                                                      if lcs /= v_ty then let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                                          in
                                                                                            throwE ((Internal_error errmsg):err_lok)
                                                                      else do
                                                                        let v_attr_new = Sym_attrib {sym_attr_geometry = (-1, -1), sym_attr_entity = syn_node_promote v_attr lcs}
                                                                        let (r_mod, err_mod) = sym_modify (symtbl', h) v_id v_attr_new
                                                                        case sym_internalerr err_mod of
                                                                          (e:_, _) -> throwE $ err_lok ++ err_mod ++ [Internal_error errmsg]
                                                                            where
                                                                              errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                          ([], _) -> case r_mod of
                                                                            Just ((a, _), symtbl'') | (a == v_attr_new) -> return ((((v_id, lcs), (Just lcs, Just v_ty_decl'))), symtbl'', err')
                                                                              where
                                                                                errmsg = "Variable " ++ v_id ++ " has insufficient type in declaration, implicitly promoted to " ++
                                                                                         (show lcs) ++ " from " ++ (show v_ty_decl') ++ "."
                                                                                err' = err_lok ++ err_mod ++ [Type_constraint_mismatched errmsg]
                                                                    Nothing -> if v_ty_decl' /= v_ty then return (((v_id, v_ty_decl'), (Nothing, Just v_ty_decl')), symtbl', err_lok)
                                                                               else
                                                                                 let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                                 in
                                                                                   throwE $ err_lok ++ [Internal_error errmsg]
                                                                 )
          _ -> throwE ((Internal_error errmsg):err_lok)
            where
              errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
      )

ty_prom_var_decl :: Symtbl -> [Ty_env_bind] -> ExceptT (([Ty_env_bind], ([Prom], [Subst])), Symtbl, [Error_codes]) IO (([Ty_env_bind], ([Prom], [Subst])), Symtbl, [Error_codes])
ty_prom_var_decl symtbl binds =
  Prelude.foldl (\env -> \(v_id, v_ty) -> do
                    (env'@(bs, (ps, ss)), stbl, es) <- env
                    r_p <- lift $ runExceptT $ ty_chk_var_decl stbl (v_id, v_ty)
                    case r_p of
                      Left e -> throwE (env', stbl, es ++ e)
                      Right (((v_id', v_ty'), (ty_prom, ty_decl)), stbl', e) ->
                        if (v_id' /= v_id) then
                          let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                          in
                            throwE (env', stbl', (Internal_error errmsg):(es ++ e))
                        else
                         case ty_decl of
                           Nothing -> throwE (env', stbl', (Internal_error errmsg):(es ++ e))
                             where
                               errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                           Just _ -> let errmsg = "Valriable " ++ v_id ++ " should be declared with the type of " ++ (show v_ty) ++ "."
                                         e' = e ++ (if v_ty' == v_ty then [] else [Type_constraint_mismatched errmsg])
                                     in
                                       return (case ty_prom of
                                                 Just prom -> ((bs, ((v_id, (ty_decl, prom)):ps, ss)), stbl', es ++ e')
                                                 Nothing -> ((bs, (ps, ss)), stbl', es ++ e')
                                              )
                ) (return ((binds, ([], [])), symtbl, [])) binds


ty_inf_var :: Symtbl -> ((String, Type), Syntree_node) -> ExceptT ((Ty_env, Syntree_node), Symtbl, [Error_codes]) IO ((Ty_env, Syntree_node), Symtbl, [Error_codes])
ty_inf_var symtbl ((v_id, v_ty), expr) =
  do
    let env_decl ((v_id, v_ty), (v_ty_prom, v_ty_decl)) = [([(v_id, v_ty)], (case v_ty_prom of
                                                                                Nothing -> ([], [])
                                                                                Just ty_prom -> ([(v_id, (v_ty_decl, ty_prom))], [])
                                                                            )
                                                           )]
    r_decl <- lift $ runExceptT $ ty_chk_var_decl symtbl (v_id, v_ty)
    case r_decl of
      Left err -> throwE ((Ty_env [([(v_id, v_ty)], ([],[]))], expr), symtbl, (Internal_error errmsg):err)
        where
          errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
      Right ((decl@((v_id', v_ty'), (v_ty_prom, v_ty_decl))), symtbl', err) ->
        if v_id' /= v_id then
          let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
          in
            throwE ((Ty_env [([(v_id, v_ty)], ([],[]))], expr), symtbl', (Internal_error errmsg):err)
        else do
          let errmsg_decl = "Variable " ++ v_id ++ " is expected to have the type of " ++ (show v_ty) ++ "."
          let e_bin = env_decl decl
          let env = Ty_env e_bin
          let equ = (v_ty, v_ty')
          case ty_unif [equ] of
            Just [] -> return ((env, expr), symtbl', err)
            Just u_var -> do
              let v_ty'' = ty_subst u_var v_ty'
              let expr' = Syn_var v_id v_ty''
              let e_bin' = ([(v_id, v_ty'')], ([], u_var)):e_bin
              let env' = Ty_env e_bin'
              r_mod <- lift $ runExceptT $ ty_chk_var_decl symtbl' (v_id, v_ty'')
              case r_mod of
                Left err_mod -> throwE ((env', expr'), symtbl', (Internal_error errmsg):(err ++ err_mod))
                  where
                    errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                Right (((v_id'', mod_ty), (mod_ty_prom, mod_ty_decl)), symtbl'', err_mod) ->
                  if v_id'' /= v_id then let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                         in
                                           throwE ((env', expr'), symtbl'', (Internal_error errmsg):(err ++ err_mod))
                  else do
                    let err' = err ++ err_mod
                    case mod_ty_decl of
                      Nothing -> throwE ((env', expr'), symtbl'', (Internal_error errmsg):err')
                        where
                          errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                      Just v_ty_decl' | v_ty_decl' == (case v_ty_decl of
                                                         Nothing -> v_ty'
                                                         Just ty_decl -> (case v_ty_prom of
                                                                            Just ty_prom -> ty_prom
                                                                            Nothing -> ty_decl
                                                                         )
                                                      ) -> if mod_ty == v_ty'' then return ((env'', expr'), symtbl'', err')
                                                           else
                                                             return ((env'', expr'), symtbl'', err' ++ [Type_constraint_mismatched errmsg_decl])
                        where
                          env'' = case mod_ty_prom of
                                    Just ty_prom -> Ty_env (([(v_id, mod_ty)], ([(v_id, (mod_ty_decl, ty_prom))], [])):e_bin')
                                    Nothing -> env'
                      
                      _ -> throwE ((env', expr'), symtbl'', (Internal_error errmsg):err')
                        where
                          errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
              
            Nothing -> return ((env, expr), symtbl', (Type_constraint_mismatched errmsg_decl):err)

ty_inf_expr :: Symtbl -> Syntree_node -> ExceptT ((Ty_env, Syntree_node), Symtbl, [Error_codes]) IO ((Ty_env, Syntree_node), Symtbl, [Error_codes])
ty_inf_expr symtbl expr =
  case expr of
    Syn_val (Val_bool b) ty_b -> if ty_b == Ty_bool then return ((Ty_env [], expr), symtbl, [])
                                 else let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                      in
                                        throwE ((Ty_env [], expr), symtbl, [Internal_error errmsg])
    Syn_val (Val_int n) ty_n -> if (ty_n == Ty_int) then return ((Ty_env [], expr), symtbl, [])
                                else let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                     in
                                       throwE ((Ty_env [], expr), symtbl, [Internal_error errmsg])
    Syn_val (Val_str s) ty_s -> if (ty_s == Ty_string) then return ((Ty_env [], expr), symtbl, [])
                                else let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                     in
                                       throwE ((Ty_env [], expr), symtbl, [Internal_error errmsg])
    Syn_var v_id v_ty -> ty_inf_var symtbl ((v_id, v_ty), expr)
    
    Syn_expr_asgn expr_l expr_r ty -> do
      ((env_r, expr_r_inf), symtbl_r, err_r) <- ty_inf symtbl expr_r
      ((env_l@(Ty_env l_bs), expr_l_inf), symtbl_rl, err_l) <- ty_inf symtbl_r expr_l
      let err = err_r ++ err_l
      
      lift $ (do
                 putStrLn $ "(l-ty, r-ty): " ++ "(" ++ (show $ syn_node_typeof expr_l_inf) ++ ", " ++ (show $ syn_node_typeof expr_r_inf) ++ ")"
                 return $ Left ((env_l, expr_l_inf), symtbl_rl, err_l)
             )
      
      case expr_l_inf of
        Syn_var l_v_id l_v_ty -> do
          l_env_bs <- case l_bs of
                        (bs, _):_ | bs /= [] -> return l_bs
                        _ -> throwE ((ty_ovwt_env env_r env_l, Syn_expr_asgn expr_l_inf expr_r_inf (syn_node_typeof expr_l_inf)), symtbl_rl, err)
          
          r_ty_asgn <- lift $ case ty_lcs (syn_node_typeof expr_r_inf) (syn_node_typeof expr_l_inf) of
                                Just lcs' ->return $ Right (((env_l, expr_l_inf), (env_r, syn_node_promote expr_r_inf lcs')), symtbl_rl, [])
                                Nothing -> (case ty_lcs (syn_node_typeof expr_l_inf) (syn_node_typeof expr_r_inf) of
                                              Just lcs' -> do
                                                l_mod <- runExceptT $ ty_chk_var_decl symtbl_rl (l_v_id, (syn_node_typeof expr_r_inf))
                                                case l_mod of
                                                  Left err_mod -> return $ Left (((env_l, expr_l_inf), (env_r, expr_r_inf)), symtbl_rl, err_mod ++ [Internal_error errmsg])
                                                    where
                                                      errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                  
                                                  Right (((l_v_id', l_v_ty'), (v_ty_prom, v_ty_decl)), symtbl_rl', err_mod) ->
                                                    if (l_v_id' /= l_v_id) || not (isJust $ ty_lcs (syn_node_typeof expr_r_inf) l_v_ty') then
                                                      let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                      in
                                                        return $ Left (((env_l, expr_l_inf), (env_r, expr_r_inf)), symtbl_rl', err_mod ++ [Internal_error errmsg])
                                                    else
                                                      case v_ty_prom of
                                                        Nothing -> return $ Right (((env_l, expr_l_inf), (env_r, expr_r_inf)), symtbl_rl', err')
                                                          where
                                                            err' = [Type_constraint_mismatched errmsg_decl] ++ err_mod
                                                        Just ty_prom -> do
                                                          r_l' <- runExceptT $ ty_inf symtbl_rl' expr_l
                                                          case r_l' of
                                                            Left ((env_l', expr_l_inf'), symtbl_rl'', err_l') ->
                                                              return $ Left (((env_l', expr_l_inf'), (env_r, expr_r_inf)), symtbl_rl'', err')
                                                              where
                                                                err' = [Type_constraint_mismatched errmsg_decl] ++ err_mod ++ err_l'
                                                            Right ((env_l', expr_l_inf'), symtbl_rl'', err_l') ->
                                                              return $ Right (((env_l', expr_l_inf'), (env_r, expr_r_inf)), symtbl_rl'', err')
                                                              where
                                                                err' = [Type_constraint_mismatched errmsg_decl] ++ err_mod ++ err_l'
                                                    where
                                                      errmsg_decl = "Valriable " ++ l_v_id ++ " should be declared with the type of " ++ (show $ syn_node_typeof expr_r_inf) ++ "."
                                              
                                              Nothing -> return $ Right (((env_l, expr_l_inf), (env_r, expr_r_inf)), symtbl_rl, [])
                                           )
          case r_ty_asgn of
            Left (((env_l', expr_l_inf'), (env_r', expr_r_inf')), symtbl_rl', err_ty_asgn) ->
              throwE ((ty_ovwt_env env_r' env_l', Syn_expr_asgn expr_l_inf' expr_r_inf' (syn_node_typeof expr_l_inf')), symtbl_rl', err ++ err_ty_asgn)
            Right (((env_l', expr_l_inf'), (env_r', expr_r_inf')), symtbl', err_ty_asgn) -> do
              let err' = err ++ err_ty_asgn
              let ((env_l'', env_r''), equ_env) = ty_equ_envs env_l' env_r'
              let equ_asgn = (syn_node_typeof expr_l_inf', syn_node_typeof expr_r_inf')
              case ty_unif (equ_env ++ [equ_asgn]) of
                Just u_asgn -> do
                  let env_r_inf = ty_subst_env' u_asgn env_r''
                      expr_r_inf'' = syn_node_subst u_asgn expr_r_inf'
                      env_l_inf = ty_subst_env' u_asgn env_l''
                      expr_l_inf'' = syn_node_subst u_asgn expr_l_inf'
                  let symtbl'' = sym_subst u_asgn symtbl'
                  r <- lift $ do
                    r'@((en, Syn_expr_asgn e_l e_r t_asgn), stbl, es) <-
                      case ty_merge_env env_l_inf env_r_inf of
                        Just env_merged -> return ((env_merged, Syn_expr_asgn expr_l_inf'' expr_r_inf'' (syn_node_typeof expr_l_inf'')), symtbl'', err')
                        Nothing -> return ((ty_ovwt_env env_r_inf env_l_inf, Syn_expr_asgn expr_l_inf'' expr_r_inf'' (syn_node_typeof expr_l_inf'')), symtbl', err'')
                          where
                            errmsg = "ill unification detected in type reconstruction."
                            err'' = err ++ [Type_constraint_mismatched errmsg]
                    putStrLn $ show u_asgn
                    return $ Right r'
                  case r of
                    Left r' -> throwE r'
                    Right r' -> return r'
                
                Nothing -> return ((ty_ovwt_env env_r env_l, Syn_expr_asgn expr_l_inf expr_r_inf (syn_node_typeof expr_l_inf)), symtbl', (err ++ [Type_constraint_mismatched errmsg]))
                  where
                    errmsg = "Left-handside expression must have supertype of r.h.s. in assignment expression."
        _ -> return ((ty_ovwt_env env_r env_l, Syn_expr_asgn expr_l_inf expr_r_inf (syn_node_typeof expr_l_inf)), symtbl_rl, (err ++ [Ill_formed_expression errmsg]))
          where
            errmsg = "Left expression must be lvalue in assignment expression."
    
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
            Nothing -> let ((env_cond'', env_true'), equs_cond_true) = ty_equ_envs env_cond env_true
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
              let ((env_cond'', env_true'), equs_cond_true) = ty_equ_envs env_cond env_true
              let ((env_cond''', env_false'), equs_cond_false) = ty_equ_envs env_cond'' env_false
              let ((env_true'', env_false''), equs_true_false) = ty_equ_envs env_true' env_false'
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
      r_0 <- lift $ runExceptT $ ty_inf symtbl expr0
      case r_0 of
        Left ((env0, expr0_inf), symtbl', err0) ->  throwE ((env0, expr'), symtbl', err0)
          where
            expr' = Syn_expr_par expr0_inf (syn_node_typeof expr0_inf)
        Right ((env0, expr0_inf), symtbl', err0) -> (case expr0_inf of
                                                       Syn_val _ _ -> return $ ((env0, expr'), symtbl', err0)
                                                       Syn_var _ _ -> return $ ((env0, expr'), symtbl', err0)
                                                       --Syn_expr_asgn _ _ _ -> return $ ((env0, expr'), symtbl', err0)
                                                       Syn_expr_par _ _ -> return $ ((env0, expr'), symtbl', err0)
                                                       Syn_expr_call _ _ _ -> return $ ((env0, expr'), symtbl', err0)
                                                       Syn_expr_una _ _ _ -> return $ ((env0, expr'), symtbl', err0)
                                                       Syn_expr_bin _ _ _ -> return $ ((env0, expr'), symtbl', err0)
                                                       _ -> return $ ((env0, expr'), symtbl', err0)
                                                         where
                                                           errmsg = "parentheses expects expression."
                                                           err' = err0 ++ [Type_constraint_mismatched errmsg]
                                                    )
          where
            expr' = Syn_expr_par expr0_inf (syn_node_typeof expr0_inf)
    
    Syn_expr_una ope expr0 ty -> do
      r_e0 <- lift $ runExceptT (ty_inf_expr symtbl expr0)
      case r_e0 of
        Right ((env0, e0_inf), symtbl', err) -> (case (ope, (syn_node_typeof e0_inf)) of
                                                   (Ope_decre, ty0) -> (case ty0 of
                                                                          Ty_int -> return ((env0, Syn_expr_una Ope_decre e0_inf Ty_int), symtbl', err)
                                                                          _ -> return ((env0, Syn_expr_una Ope_decre e0_inf ty0), symtbl', err')
                                                                            where
                                                                              errmsg = "Cannot increment/decrement the expression with type of " ++ (show ty0) ++ "."
                                                                              err' = err ++ [Type_constraint_mismatched errmsg]
                                                                       )
                                                   (Ope_incre, ty0) -> (case ty0 of
                                                                          Ty_int -> return ((env0, Syn_expr_una Ope_incre e0_inf Ty_int), symtbl', err)
                                                                          _ -> return ((env0, Syn_expr_una Ope_incre e0_inf ty0), symtbl', err')
                                                                            where
                                                                              errmsg = "Cannot increment/decrement the expression with type of " ++ (show ty0) ++ "."
                                                                              err' = err ++ [Type_constraint_mismatched errmsg]
                                                                       )
                                                   (Ope_neg, ty0) -> (case ty0 of
                                                                        Ty_int -> return ((env0, Syn_expr_una Ope_neg e0_inf Ty_int), symtbl', err)
                                                                        _ -> return ((env0, Syn_expr_una Ope_neg e0_inf ty0), symtbl', err')
                                                                          where
                                                                            errmsg = "Cannot negate the expression with type of " ++ (show ty0) ++ "."
                                                                            err' = err ++ [Type_constraint_mismatched errmsg]
                                                                     )
                                                   _ -> throwE ((env0, Syn_expr_una ope e0_inf (syn_node_typeof e0_inf)), symtbl', err')
                                                     where
                                                       errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                       err' = (Internal_error errmsg):err
                                                )
        Left ((env0, e0_inf), symtbl', err) -> throwE ((env0, Syn_expr_una ope e0_inf (syn_node_typeof e0_inf)), symtbl', err)
    
    Syn_expr_bin ope (expr1, expr2) ty -> do     
      ((env1, expr1_inf), symtbl_1, err1) <- do
        r_1 <- lift $ runExceptT $ ty_inf_expr symtbl expr1
        case r_1 of
          Right r' -> return r'
          Left ((env1', e1_inf), symtbl', e1_err) -> throwE ((env1', e1_inf'), symtbl', e1_err)
            where
              e1_inf' = Syn_expr_bin ope (e1_inf, expr2) (syn_node_typeof e1_inf)
      
      ((env2, expr2_inf), symtbl_2, err2) <- do
        r_2 <- lift $ runExceptT $ ty_inf_expr symtbl_1 expr2
        case r_2 of
          Right r' -> return r'
          Left ((env2', e2_inf), symtbl', e2_err) -> throwE (((ty_ovwt_env env2' env1), e2_inf'), symtbl', (err1 ++ e2_err))
            where
              e2_inf' = Syn_expr_bin ope (expr1_inf, e2_inf) (syn_node_typeof e2_inf)
      let err = err1 ++ err2
      
      let ((expr1_inf', expr2_inf'), lcs) = case ty_lcs (syn_node_typeof expr2_inf) (syn_node_typeof expr1_inf) of
                                              Just lcs' -> ((expr1_inf, syn_node_promote expr2_inf lcs'), Just lcs')
                                              Nothing -> (case ty_lcs (syn_node_typeof expr1_inf) (syn_node_typeof expr2_inf) of
                                                            Just lcs' -> ((syn_node_promote expr1_inf lcs', expr2_inf), Just lcs')
                                                            Nothing -> ((expr1_inf, expr2_inf), Nothing)
                                                         )
      case lcs of
        Just _ | (syn_node_typeof expr1_inf') /= (syn_node_typeof expr2_inf') ->
                 throwE ((ty_ovwt_env env1 env2, (Syn_expr_bin ope (expr1_inf', expr2_inf') (syn_node_typeof expr2_inf'))), symtbl_2, (Internal_error errmsg):err)
          where
            errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
        _ -> do  
          let equ_bin_op = ((syn_node_typeof expr1_inf'), (syn_node_typeof expr2_inf'))
          let ((env1', env2'), equ_env) = ty_equ_envs env1 env2
          --lift $ putStrLn ("equations: " ++ (show equ_bin_op) ++ (show equ_env))
          
          let r_u = case ty_unif (equ_env ++ [equ_bin_op]) of
                      Just u_bin -> let expr1_inf'' = syn_node_subst u_bin expr1_inf'
                                        expr2_inf'' = syn_node_subst u_bin expr2_inf'
                                    in
                                      case ty_merge_env (ty_subst_env u_bin env1') (ty_subst_env u_bin env2') of
                                        Just env' -> Right $ Right ((env', (Syn_expr_bin ope (expr1_inf'', expr2_inf'') (syn_node_typeof expr2_inf''))), symtbl_2, err)
                                        Nothing -> Left ((env', (Syn_expr_bin ope (expr1_inf'', expr2_inf'') (syn_node_typeof expr2_inf''))), symtbl_2, (Internal_error errmsg):err)
                                          where
                                            env' = ty_ovwt_env (ty_subst_env u_bin env1') (ty_subst_env u_bin env2')
                                            errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                      
                      Nothing -> Right $ Left ((env', (Syn_expr_bin ope (expr1_inf', expr2_inf') (syn_node_typeof expr2_inf'))), symtbl_2, err ++ [Type_constraint_mismatched errmsg])
                        where
                          env' = ty_ovwt_env env1' env2'
                          errmsg = "Type environments of operands doesn't meet, in binary operation of " ++ (show ope)
          
          case r_u of
            Left u -> throwE u
            Right u -> (case u of
                          Left u' -> return u'
                          Right (u'@((Ty_env [], expr_bin_inf), symtbl', err')) -> return u'
                          Right ((Ty_env ((bs', (ps', ss')):bss'), expr_bin_inf), symtbl', err') -> do
                            r_mod <- lift $ runExceptT $ ty_prom_var_decl symtbl' bs'
                            case r_mod of
                              Left (bs_mod, symtbl'', err_mod) -> throwE ((Ty_env (bs_mod:((bs', (ps', ss')):bss')), expr_bin_inf), symtbl'', err' ++ err_mod)
                              Right (bs_mod, symtbl'', err_mod) -> return ((Ty_env (bs_mod:((bs', (ps', ss')):bss')), expr_bin_inf), symtbl'', err' ++ err_mod)
                       )
    
    _ -> return ((Ty_env [], expr), symtbl, [])

{- ty_inf :: Symtbl -> Syntree_node -> ExceptT ((Ty_env, Syntree_node), Symtbl, [Error_codes]) IO ((Ty_env, Syntree_node), Symtbl, [Error_codes])
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
    
    _ -> return ((Ty_env [], decl), symtbl, []) -- Syn_none -}

ty_inf :: Symtbl -> Syntree_node -> ExceptT ((Ty_env, Syntree_node), Symtbl, [Error_codes]) IO ((Ty_env, Syntree_node), Symtbl, [Error_codes])
ty_inf symtbl expr =
  case expr of
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
                                                          let ((env_seq', env_next'), equ_env_seq') = ty_equ_envs env_seq env_next
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
    
    Syn_val _ _ -> ty_inf_expr symtbl expr
    Syn_var _ _ -> ty_inf_expr symtbl expr
    Syn_expr_asgn _ _ _ -> ty_inf_expr symtbl expr
    Syn_expr_par _ _ -> ty_inf_expr symtbl expr
    
    --Syn_expr_call _ _ _ -> ty_inf_expr symtbl expr
    Syn_expr_call fun_id args ty -> do
      case sym_lkup_fun_decl symtbl fun_id of
        --Nothing -> throwE ((Ty_env [], expr), symtbl, [Undefined_symbol errmsg])
        (Nothing, err_lok) -> throwE ((Ty_env [], expr), symtbl, (err_lok ++ [Undefined_symbol errmsg]))
          where
            errmsg = "undefined function calling of : " ++ fun_id ++ "."
        --Just (Sym_attrib { sym_attr_entity = fun_attr}, symtbl') ->
        (Just ((Sym_attrib { sym_attr_entity = fun_attr}, h), symtbl'), err_lok) ->
          (case fun_attr of
             -- e.g. func1 (j as int, b as bool) as int { ... }
             --        f_id: func1
             --        f_args: j as int, b as bool
             --        f_body: { ... }
             --        f_ty: Ty_fun [Ty_int, Ty_bool] Ty_int, s.t. "(j as int, b as bool) as int".
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
                                      let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
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
                                                --Right ((Ty_env [], Syn_expr_call fun_id [] (Ty_fun args_ty f_ty)), symtbl'', errs_args)
                                                Right ((Ty_env [([(fun_id, Ty_fun args_ty f_ty)], ([], []))], Syn_expr_call fun_id [] (Ty_fun args_ty f_ty)), symtbl'', errs_args)
                                        _ -> let args' = Prelude.map snd judges_args
                                                 --env_call = make_env_ovwt (Prelude.map fst judges_args)
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
                                                                                  let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                                  Left ((env_call_inf, Syn_expr_call fun_id f_args_inf ty'), symtbl'', (errs_args ++ [Internal_error errmsg]))
                                                                                )
                                                           Left (ty'@(Ty_fun _ f_ty'), _) ->
                                                             let env_call_inf = make_env_ovwt envs_arg_inf
                                                             in
                                                               assert False (
                                                                 do
                                                                   let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
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
                                                                 let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
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
                                                  equs = zip ty_params ty_args
                                                  equs' = Prelude.foldl (\es -> \(ty_p, ty_a) -> es ++ (if (ty_p == ty_a) then [] else [(ty_p, ty_a)])) [] equs
                                              in
                                                assert ((length ty_params) == (length ty_args)) equs'
                                            union_binds envs =
                                              case envs of
                                                [] -> []
                                                (Ty_env []):es -> union_binds es
                                                (Ty_env ((bs, _):_)):es -> Set.toList $ Set.union (Set.fromList bs) (Set.fromList (union_binds es))
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
                                                g:gs -> (Set.toList (enum_equs' g)) ++ (gen_equs gs)
                                                  where
                                                    enum_equs' binds =
                                                      case binds of
                                                        [] -> Set.fromList []
                                                        (v_id, ty):bs -> Set.union (Set.fromList equs) (enum_equs' bs)
                                                          where
                                                            equs = Prelude.foldl (\es -> \(v_id', ty') -> assert (v_id' /= v_id) (if (ty' == ty) then (es ++ [(ty, ty')]) else es)) [] bs
                           
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
             _ -> throwE ((Ty_env [], expr), symtbl', (Internal_error errmsg):err_lok)
               where
                 errmsg = "Function calling must be applied on function objects."
          )
        --Just _ ->
        (Just _, _ ) -> assert False (
          do
            let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
            throwE ((Ty_env [], expr), symtbl, [Internal_error errmsg])
          )
    Syn_cond_expr _ _ -> ty_inf_expr symtbl expr
    Syn_expr_una _ _ _ -> ty_inf_expr symtbl expr
    Syn_expr_bin _ _ _ -> ty_inf_expr symtbl expr
    
    --case Syn_tydef_decl _ _ -> INTERNAL ERROR
    --case Syn_arg_decl _ _ -> INTERNAL ERROR
    --case Syn_rec_decl _ _ -> INTERNAL ERROR
    --case Syn_var_decl _ _ -> INTERNAL ERROR
    
    _ -> return ((Ty_env [], expr), symtbl, []) -- Syn_none


show_internalerr :: [Error_codes] -> IO ()
show_internalerr errs =
  mapM_ putStrLn $ Prelude.foldl (\s -> \e -> (case e of
                                                 Internal_error msg -> s ++ [msg]
                                                 _ -> s
                                              )
                                 ) [] errs

compile :: [Tk_code] -> IO ((Maybe [Syntree_node], [Error_codes]), Symtbl, [Tk_code])
compile tokens =
  let comp_main symtbl (tokens, errs) =
        case tokens of
          [] -> return $ Right (([], errs), symtbl, [])
          --(Tk_smcl:ts) -> comp_main symtbl (ts, errs)
          ts -> do
            r <- runExceptT $ cons_ptree symtbl ts (True, True, True, True)
            case r of
              Right ((syn_tree, symtbl', ts'), err) -> (case syn_tree of
                                                          Just s_tree -> do
                                                            let (stbl0, err0) = adjust_scope (sym_leave_scope symtbl' Sym_cat_decl) (Sym_cat_decl, 1)
                                                            case sym_internalerr err0 of
                                                              (e:_, _) -> show_internalerr err0 >> (return $ Left ())
                                                              _ -> if (sym_crnt_level $ sym_scope_right (sym_categorize stbl0 Sym_cat_decl)) /= 0 then
                                                                     let errmsg = __FILE__ ++ ":" ++ (show (__LINE__ :: Int))
                                                                     in
                                                                       show_internalerr (errs ++ err ++ err0 ++ [Internal_error errmsg]) >> (return $ Left ())
                                                                   else
                                                                     do
                                                                       let (stbl1, err1) = sym_enter_scope (Just stbl0) Sym_cat_decl
                                                                       case sym_internalerr err1 of
                                                                         (e:_, _) -> show_internalerr err1 >> (return $ Left ())
                                                                         _ -> do
                                                                           let errs' = errs ++ err ++ err0 ++ err1
                                                                           rs <- comp_main stbl1 (ts', errs')
                                                                           return $ case rs of
                                                                                      Right ((s_ts, errs''), symtbl'', ts'') -> Right ((s_tree:s_ts, errs''), symtbl'', ts'')
                                                                                      _ -> Left ()
                                                          _ -> return $ Right (([], (errs ++ err)), symtbl', ts')
                                                       )
                where
                  adjust_scope :: (Symtbl, [Error_codes]) -> (Sym_category, Scope_Lv) -> (Symtbl, [Error_codes])
                  adjust_scope (symtbl, errs) (cat, lv) =
                    if (sym_crnt_level $ sym_scope_right (sym_categorize symtbl cat)) <= lv then (symtbl, errs)
                    else
                      case sym_leave_scope symtbl cat of
                        (symtbl', es) -> (case sym_internalerr es of
                                            (e:_, _) -> (symtbl', errs ++ es)
                                            _ -> adjust_scope (symtbl', errs ++ es) (cat, lv - 1)
                                         )
              Left err_exc -> do
                print_excepts [err_exc]
                return $ Left ()
              where
                print_excepts :: [Error_Excep] -> IO ()
                print_excepts errs = forM_ (Prelude.foldl (\s -> \e -> (s ++ (case e of
                                                                                Error_Excep Excep_assert_failed assert_msg -> [assert_msg]
                                                                                Error_Excep _ errmsg -> [errmsg]
                                                                             )
                                                                       )
                                                          ) [] errs
                                           ) putStrLn
  in
    do
      let (symtbl, err1) = sym_enter_scope Nothing Sym_cat_decl
      case sym_internalerr err1 of
        (e:_, _) -> show_internalerr err1 >> return ((Nothing, err1), symtbl, tokens)
        _ -> do
          r <- comp_main symtbl (tokens, err1)
          case r of
            Left _ -> return ((Nothing, []), symtbl, tokens)
            Right ((syn_trees, errs), symtbl', tokens') -> return ((Just syn_trees, errs), symtbl', tokens')


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
  h <- openFile "src4.txt" ReadMode
  src <- read_src h
  
  let (tokens, src_remains) = conv2_tokens src
  putStrLn $ "source:  " ++ (show src)
  putStrLn $ "tokens:  " ++ (show (tokens, src_remains))
  putStrLn ""
  
  {- let (symtbl, err0) = sym_enter_scope Nothing Sym_cat_decl
  ((syn_forest, err_par), symtbl', tokens') <- do
    case sym_internalerr err0 of
      (e:es, err0') -> do
        show_internalerr (e:es) >> return ((Nothing, []),symtbl, tokens)
      ([], erro') -> do
        r <- (do
                 r <- runExceptT $ cons_ptree symtbl tokens (True, True, True)
                 case r of
                   Left err_exc -> (do
                                       print_excepts err_exc
                                       return $ Left ()
                                   )
                   Right ((syn_tree, symtbl', tokens'), err1) -> do
                     case syn_tree of
                       Just s_tree -> do
                         r_ts <- cons_p_trees symtbl' tokens'
                         return (case r_ts of
                                   Right ((s_ts, errs), symtbl'', tokens'') -> Right ((Just (s_tree:s_ts), (err0 ++ err1 ++ errs)), symtbl'', tokens'')
                                   _ -> Left ()
                                )
                       _ -> return $ Right ((Nothing, (err0 ++ err1)), symtbl', tokens')
                     
                       where
                         cons_p_trees symtbl tokens =
                           case tokens of
                             [] -> return $ Right (([], []), symtbl, [])
                             (Tk_smcl:ts) -> do
                               r <- runExceptT $ cons_ptree symtbl ts (True, True, True)
                               case r of
                                 Left err_exc -> (do
                                                     print_excepts err_exc
                                                     return $ Left ()
                                                 )
                                 Right ((syn_tree, symtbl', ts'), err) -> (case syn_tree of
                                                                             Just s_tree -> do
                                                                               r_ts <- cons_p_trees symtbl' ts'
                                                                               return (case r_ts of
                                                                                         Right ((s_trees, errs), symtbl'', ts'') -> Right ((s_tree:s_trees, (err ++ errs)), symtbl'', ts'')
                                                                                         _ -> Left ()
                                                                                      )
                                                                             _ -> return $ Right (([], err), symtbl', ts')
                                                                          )
                             ts -> return $ Right (([], []), symtbl, ts)
             )
        case r of
          Left _ -> return ((Nothing, []), symtbl, tokens)
          Right r' -> return r' -}
  ((syn_forest, err_par), symtbl', tokens') <- compile tokens
  putStrLn $ "p-trees: " ++ (show (syn_forest, tokens'))
  case err_par of
    [] -> return ()
    _ -> putStr "\n" >> putStr "Errors:" >> forM_ (Prelude.map show err_par) (putStrLn . ((++) "  "))
  putStrLn ""
  putStr "reconstruction:" >> mapM_ (putStrLn . (++) "  ") (case syn_forest of
                                                              Nothing -> []
                                                              Just ss -> Prelude.foldl (\str -> \s -> (str ++ [recons_src symtbl' s])) [] ss
                                                           )
  putStrLn ""
  
  {- putStr "ty-raw:  "
  ty_curved <- case syn_forest of
                 Just s_trees -> do
                   r <- runMaybeT $ Prelude.foldl (\stmts_tv -> (\stmt -> do
                                                                    (stmts, stbl) <- stmts_tv
                                                                    r' <- lift (do
                                                                                   r_cur <- runExceptT $ ty_curve stbl stmt
                                                                                   case r_cur of
                                                                                     Left err -> do
                                                                                       Prelude.foldl (\u -> \e -> putStrLn (show e)) (return ()) err
                                                                                       return $ Nothing
                                                                                     Right (stmt', stbl') -> return $ Just (stmts ++ [stmt'], stbl')
                                                                               )
                                                                    case r' of
                                                                      Nothing -> mzero
                                                                      Just r'' -> return r''
                                                                )
                                                  ) (return ([], symtbl')) s_trees
                   case r of
                     Nothing -> return []
                     Just (s_trees', _) -> return s_trees'
  mapM_ putStrLn $ Prelude.map show ty_curved
  putStrLn "" -}
  
  putStr "simtbl_before:  "
  --print_symtbl symtbl' Sym_cat_decl
  print_symtbl symtbl' Sym_cat_func
  putStrLn ""
  
  {- putStr "ty-inf:  "
  (judges_inf, symtbl'', errs) <- do
    r <- runExceptT $ Prelude.foldl (\js -> \t_raw -> do
                                        (judges, stbl, errs) <- js
                                        ((env, t_inf), stbl', errs') <- ty_inf stbl t_raw
                                        return (case judges of
                                                  [] -> ([(env, t_inf)], stbl', (errs ++ errs'))
                                                  _ -> ((judges ++ [(env, t_inf)]), stbl', (errs ++ errs'))
                                               )
                                    ) (return ([], symtbl', [])) ty_curved
    return (case r of
              Right r -> r
              Left ((env, t_inf), symtbl', errs) -> ([(env, t_inf)], symtbl', errs)
           )
  mapM_ putStrLn $ Prelude.map show judges_inf
  putStrLn "" -}
  
  --putStr "simtbl_after:  "
  -- --print_symtbl symtbl' Sym_cat_decl
  --print_symtbl symtbl' Sym_cat_func
    
    where
      read_src :: Handle -> IO String
      read_src h = do
        eof <- hIsEOF h
        if eof then return []
          else do
          str <- hGetLine h
          str' <- read_src h
          return $ str ++ str'
      
      {- show_internalerr :: [Error_codes] -> IO ()
      show_internalerr err =
        mapM_ putStrLn $ Prelude.foldl (\s -> \e -> (case e of
                                                       Internal_error msg -> s ++ [msg]
                                                       _ -> s
                                                    )
                                       ) [] err
      
      print_excepts :: Error_Excep -> IO ()
      print_excepts err = do
        let errmsg = case err of
                       Error_Excep Excep_assert_failed assert_msg -> assert_msg
                       Error_Excep _ errmsg -> errmsg
        putStrLn errmsg
        return () -}


{- main :: IO ()  -- test code for symbol table management
main = do
  -- Lv.1
  let (symtbl, err1) = sym_enter_scope Nothing Sym_cat_decl
  case sym_internalerr err1 of
    e:es -> show_internalerr [e]
    [] -> do
      let (symtbl11, err11) = sym_regist False symtbl Sym_cat_decl ("eta", Syn_fun_decl "eta" [] (Syn_scope ([], Syn_none)) Ty_btm)
      let (symtbl12, err12) = sym_regist False symtbl11 Sym_cat_decl ("alpha", Syn_val (Val_int 1) Ty_int)
      let (symtbl13, err13) = sym_regist False symtbl12 Sym_cat_decl ("epsilon", Syn_var_decl "epsilon" Ty_string)
      
      -- Lv.2
      let (symtbl2, err2) = sym_enter_scope (Just symtbl13) Sym_cat_decl
      case  sym_internalerr err2 of
        e:es -> show_internalerr [e]
        [] -> do
          let (symtbl21, err21) = sym_regist False symtbl2 Sym_cat_decl ("beta", Syn_var_decl "beta" Ty_bool)
          let (symtbl22, err22) = sym_regist False symtbl21 Sym_cat_decl ("gamma", Syn_fun_decl "gamma" [] (Syn_scope ([], Syn_none)) Ty_btm)
          let (symtbl23, err23) = sym_regist False symtbl22 Sym_cat_decl ("zeta", Syn_fun_decl "zeta" [] (Syn_scope ([], Syn_none)) Ty_btm)
          let (symtbl24, err24) = sym_regist False symtbl23 Sym_cat_decl ("kappa", Syn_var_decl "kappa" Ty_int)
          
          -- Lv.3
          let (symtbl3, err3) = sym_enter_scope (Just symtbl24) Sym_cat_decl
          case sym_internalerr err3 of
            e:es -> show_internalerr [e]
            [] -> do
              let (symtbl31, err31) = sym_regist False symtbl3 Sym_cat_decl ("delta", Syn_var_decl "delta" Ty_bool)
              --let (symtbl31, err31) = sym_regist False symtbl3 Sym_cat_decl ("delta", Syn_val (Val_bool False) Ty_bool)
`              
              putStrLn "original: "
              print_symtbl symtbl31 Sym_cat_decl
              
              putStrLn "" >> putStrLn "" >> putStrLn "Ph.1:"
              let r31' = sym_lkup_fun_decl symtbl31 "eta"
              case r31' of
                (Just ((found, h), symtbl31'), err) -> do
                  show_internalerr err
                  putStrLn ("found: " ++ (show found))
                  let attr_new = Sym_attrib {sym_attr_geometry = (-1, -1), sym_attr_entity = Syn_fun_decl "eta" [] (Syn_scope ([], Syn_none)) Ty_top}
                  let r = sym_modify (symtbl31', h) "eta" attr_new
                  case r of
                    (Just ((attr', h'), symtbl31''), err) -> do
                      show_internalerr err
                      putStrLn ("and changed to: " ++ (show attr'))
                      putStrLn ""
                      print_symtbl symtbl31'' Sym_cat_decl
                      
                      putStrLn "" >> putStrLn "" >> putStrLn "Ph.2:"
                      let (symtbl24', err2') = sym_leave_scope symtbl31'' Sym_cat_decl
                      case sym_internalerr err2' of
                        e:es -> show_internalerr [e]
                        [] -> print_symtbl symtbl24' Sym_cat_decl
                      
                      putStrLn "" >> putStrLn "" >> putStrLn "Ph.3:"
                      let r24'' = sym_lkup_fun_decl symtbl24' "gamma"
                      case r24'' of
                        (Just ((found, h), symtbl24''), err) ->
                          do
                            case sym_internalerr err of
                              e:es -> show_internalerr [e]
                              [] -> do
                                putStrLn ("found: " ++ (show found))
                                let attr_new = Sym_attrib {sym_attr_geometry = (-1, -1), sym_attr_entity = Syn_fun_decl "gamma" [] (Syn_scope ([], Syn_none)) Ty_top}
                                let r = sym_modify (symtbl24'', h) "gamma" attr_new
                                case r of
                                  (Just ((attr', h'), symtbl24'''), err) -> do
                                    case sym_internalerr err of
                                      e:es -> show_internalerr [e]
                                      [] -> (do
                                                putStrLn ("and changed to: " ++ (show attr'))
                                                putStrLn ""
                                                print_symtbl symtbl24''' Sym_cat_decl
                                                
                                                putStrLn "" >> putStrLn "" >> putStrLn "Ph.4:"
                                                let (symtbl13', err1') = sym_leave_scope symtbl24''' Sym_cat_decl
                                                case sym_internalerr err1' of
                                                  e:es -> show_internalerr [e]
                                                  [] -> print_symtbl symtbl13' Sym_cat_decl
                                            )
                                  (Nothing, err) -> do
                                    case sym_internalerr err of
                                      e:es -> show_internalerr [e]
                                      [] -> (do
                                                putStrLn "Failed to modify!"
                                                putStrLn ""
                                                print_symtbl symtbl24'' Sym_cat_decl
                                            )
                        (Nothing, err) -> do
                          case sym_internalerr err of
                            e:es -> show_internalerr [e]
                            [] -> (do
                                      putStrLn "no registration."
                                      putStrLn ""
                                      print_symtbl symtbl24' Sym_cat_decl
                                  )
                    (Nothing, err) -> do
                      show_internalerr err
                      putStrLn "Failed to modify!"
                      putStrLn ""
                      print_symtbl symtbl31' Sym_cat_decl
                
                (Nothing, err) -> do
                  show_internalerr err
                  putStrLn "no registration."
                  putStrLn ""
                  print_symtbl symtbl31 Sym_cat_decl
  --return ()
    where
      show_internalerr :: [Error_codes] -> IO ()
      show_internalerr err =
        Prelude.mapM_ putStrLn $ Prelude.foldl (\s -> \e -> (case e of
                                                               Internal_error msg -> s ++ [msg]
                                                               _ -> s
                                                            )
                                               ) [] err
-}
