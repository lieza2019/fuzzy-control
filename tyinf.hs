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
import System.IO


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
            --Par_acc _ -> (crnt_stat, "")
            --Par_nume n -> ((Par_acc (Tk_nume n), quo_stat), "")
            Par_str -> (case quo_stat of
                          Just (No_quoted str) -> ((Par_acc (Tk_ident str), Nothing), "")
                          _ -> ((Par_err, quo_stat), "")
                       )
            --Par_keyword_as_1 -> ((Par_acc (Tk_ident "a"), Nothing), "")
            --Par_keyword_fun_false_1 -> ((Par_acc (Tk_ident "f"), Nothing), "")
            --Par_keyword_fun_2 -> ((Par_acc (Tk_ident "fu"), Nothing), "")
            --Par_keyword_false_2 -> ((Par_acc (Tk_ident "fa"), Nothing), "")
            --Par_keyword_false_3 -> ((Par_acc (Tk_ident "fal"), Nothing), "")
            --Par_keyword_false_4 -> ((Par_acc (Tk_ident "fals"), Nothing), "")
            --Par_keyword_bool_1 -> ((Par_acc (Tk_ident "b"), Nothing), "")
            --Par_keyword_bool_2 -> ((Par_acc (Tk_ident "bo"), Nothing), "")
            --Par_keyword_bool_3 -> ((Par_acc (Tk_ident "boo"), Nothing), "")
            --Par_keyword_int_1 -> ((Par_acc (Tk_ident "i"), Nothing), "")
            --Par_keyword_int_2 -> ((Par_acc (Tk_ident "in"), Nothing), "")
            --Par_keyword_true_1 -> ((Par_acc (Tk_ident "t"), Nothing), "")
            --Par_keyword_true_2 -> ((Par_acc (Tk_ident "tr"), Nothing), "")
            --Par_keyword_true_3 -> ((Par_acc (Tk_ident "tru"), Nothing), "")
            --_ -> ((Par_err, quo_stat), "")  -- including case of Par_equ_1
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
                --'-' -> (Par_acc Tk_shaft, crnt_quo_stat)
                '-' -> (Par_keyword_decre_1, crnt_quo_stat)
                --'+' -> (Par_acc Tk_cross, crnt_quo_stat)
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
  deriving (Eq, Show)

data Operation =
  Ope_asgn
  | Ope_decre
  | Ope_incre
  | Ope_neg
  | Ope_add
  | Ope_sub
  | Ope_mul
  | Ope_div
  deriving (Eq, Show)

data Val =
  Val_str String
  | Val_bool Bool
  | Val_int Integer
  deriving (Eq, Show)

data Syntree_node =
  Syn_ty_spec Type
  | Syn_scope ([Syntree_node], Syntree_node)
  | Syn_fun_decl String [Syntree_node] Syntree_node Type
  | Syn_arg_def String Type
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
  deriving (Eq, Show)

data Error_codes =
  Unknown_token_detected
  | Imcomplete_function_declaration
  | Imcomplete_type_specifier
  | Illegal_left_expression_for_assignment
  | Illegal_type_specified Tk_code
  | Illegal_operands Operation Syntree_node
  | Internal_error String
  deriving (Eq, Show)

halt :: Error_codes -> IO ()
halt err = do
  putStrLn $ show err
  return $ assert False ()


{-
cons_forest :: [Tk_code] -> [Syntree_node]
cons_forest tokens = do
  token <- tokens
  cons_tree token
    where
      cons_tree :: Tk_code -> [Syntree_node]
      cons_tree tk =
        let sn = (case tk of
                    Tk_str s -> Syn_val (Val_str s)
                    Tk_nume n -> Syn_val (Val_int n)
                    _ -> Syn_not_impl
                 )
        in
          [sn]-
-}


par_type_decl :: [Tk_code] -> (Either Error_codes Type, [Tk_code])
par_type_decl tokens =
  case tokens of
    Tk_typed_as:[] -> (Left Imcomplete_type_specifier, [])
    Tk_typed_as:ts -> (case ts of
                         Tk_bool:ts' -> (Right Ty_bool, ts')
                         Tk_int:ts' -> (Right Ty_int, ts')
                         t:ts' -> (Left (Illegal_type_specified t), ts')
                      )
    _ -> (Left (Internal_error "Calling cons_var_decl with non variable constructor."), tokens)

cons_var_decl :: Syntree_node -> [Tk_code] -> ((Maybe Syntree_node, [Tk_code]), [Error_codes])
cons_var_decl var tokens =
  case var of
    Syn_var var_id var_ty -> (case tokens of
                                Tk_typed_as:ts -> (case par_type_decl tokens of
                                                     (Right var_ty', ts') -> ((Just (Syn_var_decl var_id var_ty'), ts'), [])
                                                     (Left err, ts') -> ((Just (Syn_var_decl var_id var_ty), ts'), [err])
                                                  )
                                _ -> ((Nothing, tokens), [])
                                -- _ -> ((Syn_var var_id Ty_abs, tokens), [])
                             )
    _ -> ((Just Syn_none, tokens), [Internal_error "Calling cons_var_decl with non variable constructor."])


par_fun_decl :: Syntree_node -> [Tk_code] -> ((Syntree_node, [Tk_code]), [Error_codes])
par_fun_decl fun tokens =
  let par_fun_type tokens =
        case tokens of
          Tk_typed_as:ts -> (case par_type_decl tokens  of
                               (Right ty, ts') -> ((ty, ts'), [])
                               (Left err, ts') -> ((Ty_abs, ts'), [err])
                            )
          _ -> ((Ty_abs, tokens), [])
  in
    case fun of
      Syn_fun_decl fun_id args fun_body fun_ty -> (case tokens of
                                                     Tk_L_par:Tk_R_par:ts -> let ((fun_ty', tokens'), errs) = par_fun_type ts
                                                                             in
                                                                               ((Syn_fun_decl fun_id [] fun_body fun_ty', tokens'), errs)
                                                     Tk_L_par:ts -> let ((args', ts'), arg_errs) = cons_args_decl ts
                                                                    in
                                                                      case ts' of
                                                                        Tk_R_par:ts'' -> ((Syn_fun_decl fun_id args' fun_body fun_ty', tokens'), arg_errs ++ fun_ty_errs)
                                                                          where
                                                                            ((fun_ty', tokens'), fun_ty_errs) = par_fun_type ts''
                                                                        _ -> ((fun, ts'), (arg_errs ++ [Imcomplete_function_declaration]))
                                                       where
                                                         cons_args_decl :: [Tk_code] -> (([Syntree_node], [Tk_code]), [Error_codes])
                                                         cons_args_decl tokens =
                                                           case par_arg tokens of
                                                             (Nothing, errs) -> (([], tokens), errs)
                                                             (Just (arg, tokens'),errs) -> (case tokens' of
                                                                                              Tk_smcl:ts' -> ((arg:args, tokens''), errs ++ errs')
                                                                                                where
                                                                                                  ((args, tokens''), errs') = cons_args_decl ts'
                                                                                              _ -> (([arg], tokens'), errs)
                                                                                           )
                                                         par_arg :: [Tk_code] -> (Maybe (Syntree_node, [Tk_code]), [Error_codes])
                                                         par_arg tokens =
                                                           case tokens of
                                                             (Tk_ident arg_id):ts -> let arg = Syn_var arg_id Ty_abs
                                                                                     in
                                                                                       case cons_var_decl arg ts of
                                                                                         ((Nothing, ts'), errs) -> (Just (Syn_arg_def arg_id Ty_abs, ts'), errs)
                                                                                         ((Just (Syn_var_decl arg_id arg_ty), ts'), errs) -> (Just (Syn_arg_def arg_id arg_ty, ts'), errs)
                                                                                         ((_, ts'), errs) -> (Just (Syn_none, ts'), errs)
                                                             _ -> (Nothing, [])
                                                     
                                                     _ -> ((fun, tokens), [Imcomplete_function_declaration])
                                                  )
      _ -> ((Syn_none, tokens), [Internal_error "Calling cons_var_decl with non variable constructor."])


cons_par_tree :: [Tk_code] -> (Bool, Bool, Bool) -> (Maybe Syntree_node, [Tk_code])
cons_par_tree tokens (fun_declp, var_declp, par_contp) =
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
      cons_expr subexpr1 tokens =
        let (ope, tokens') = fetch_ope tokens
        in
          case ope of
            Nothing -> (Right subexpr1, tokens)
            Just ope' | ope' == Ope_asgn -> let left = cons_par_tree tokens' (False, False, True)
                                            in
                                              case left of
                                                (Just left_expr, tokens'') -> (Right (Syn_expr_bin Ope_asgn (subexpr1, left_expr) Ty_abs), tokens'')
                                                (Nothing, tokens'') -> (Left Illegal_left_expression_for_assignment, tokens'')
            Just ope' | is_bin_op ope' -> let r2 = cons_par_tree tokens' (False, False, True)
                                          in
                                            case r2 of
                                              (Just subexpr2, tokens'') -> (case subexpr2 of
                                                                              Syn_val _ _ -> (Right (Syn_expr_bin ope' (subexpr1, subexpr2) Ty_abs), tokens'')
                                                                              Syn_var _ _ -> (Right (Syn_expr_bin ope' (subexpr1, subexpr2) Ty_abs), tokens'')
                                                                              Syn_expr_bin bin_ope (expr_1, expr_2) _ ->
                                                                                if is_gte_op ope' bin_ope then
                                                                                  (Right (Syn_expr_bin bin_ope ((leftmost_innermst subexpr1 ope' expr_1), expr_2) Ty_abs), tokens'')
                                                                                else
                                                                                  (Right (Syn_expr_bin ope' (subexpr1, subexpr2) Ty_abs), tokens'')
                                                                              _ -> (Right (Syn_expr_bin ope' (subexpr1, subexpr2) Ty_abs), tokens'')
                                                                           )
                                              (Nothing, tokens'') -> (Left (Illegal_operands ope' Syn_none), tokens'')
            _ -> (Left (Internal_error "Invalid operator detecded, in cons_expr."), tokens)
              
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
      
      par_fun_call fun_app tokens =
        case fun_app of
          Syn_expr_call fun_id app_args app_ty -> (case tokens of
                                                     [] -> (Right fun_app, tokens)
                                                     t:ts | is_op t -> (Right fun_app, tokens)
                                                     _ -> (case cons_par_tree tokens (False, False, False) of
                                                             (Just arg, tokens') -> par_fun_call (Syn_expr_call fun_id (app_args ++ [arg]) app_ty) tokens'
                                                             (Nothing, tokens') -> (Right fun_app, tokens')
                                                          )
                                                  )
          _ -> (Left (Internal_error "Calling cons_var_decl with non variable constructor."), tokens)
  in
    let cont_par subexpr tokens =
          if par_contp then case cons_expr subexpr tokens of
                          (Right expr', tokens') -> (Just expr', tokens')
                          (Left err, tokens') -> (Nothing, tokens')
          else
            (Just subexpr, tokens)
    in     
      case tokens of
        [] -> (Nothing, [])
        Tk_L_par:ts -> (case cons_par_tree ts (False, False, True) of
                          (Just expr, (Tk_R_par:ts')) -> cont_par (Syn_expr_par expr (expr_ty expr)) ts'
                          (_, ts') -> (Nothing, ts')
                       )
        Tk_if:ts -> (case cons_par_tree ts (False, False, True) of
                       (Just cond_expr, (Tk_then:ts')) -> (case cons_par_tree ts' (False, False, True) of
                                                             (Just true_expr, (t'':ts'')) | t'' == Tk_else -> (case cons_par_tree ts'' (False, False, True) of
                                                                                                                 (Just false_expr, tokens') ->
                                                                                                                   (Just (Syn_cond_expr (cond_expr, (true_expr, Just false_expr)) Ty_abs), tokens')
                                                                                                                 (_, tokens') -> (Nothing, tokens')
                                                                                                              )
                                                             (Just true_expr, tokens') -> (Just (Syn_cond_expr (cond_expr, (true_expr, Nothing)) Ty_abs), tokens')
                                                             (_, tokens') -> (Nothing, tokens')
                                                          )
                       (_, tokens') -> (Nothing, tokens')
                    )                                        
        Tk_decre:ts -> (case ts of
                          (Tk_ident ident):ts' -> cont_par (Syn_expr_una Ope_decre (Syn_var ident Ty_abs) Ty_abs) ts'
                          _ -> (Nothing, ts)
                       )
        Tk_incre:ts -> (case ts of
                          (Tk_ident ident):ts' -> cont_par (Syn_expr_una Ope_incre (Syn_var ident Ty_abs) Ty_abs) ts'
                          _ -> (Nothing, ts)
                       )
        Tk_shaft:ts -> (case ts of
                          (Tk_ident ident):ts' -> cont_par (Syn_expr_una Ope_neg (Syn_var ident Ty_abs) Ty_abs) ts'
                          _ -> (Nothing, ts)
                       )
        Tk_false:ts -> cont_par (Syn_val (Val_bool False) Ty_bool) ts
        Tk_true:ts -> cont_par (Syn_val (Val_bool True) Ty_bool) ts
        (Tk_nume n):ts -> cont_par (Syn_val (Val_int n) Ty_int) ts
        (Tk_str s):ts -> cont_par (Syn_val (Val_str s) Ty_string) ts
        Tk_fun:ts -> if fun_declp then
          case ts of
            (Tk_ident fun_id):ts' -> 
              let fun = Syn_fun_decl fun_id [] (Syn_scope ([], Syn_none)) Ty_abs
              in
                case par_fun_decl fun ts' of
                  ((Syn_fun_decl fun_id fun_args fun_body fun_ty, Tk_L_bra:ts''), errs) ->
                    (case fun_body of
                       (Syn_scope ([], Syn_none)) -> (case (do
                                                               let ((var_decls, expr_par_trees), us) = parse_fun_body ts''
                                                                     where
                                                                       parse_fun_body :: [Tk_code] -> (([Syntree_node], [Syntree_node]), [Tk_code])
                                                                       parse_fun_body tokens =
                                                                         case cons_par_tree tokens (False, True, True) of
                                                                           (Just var_decl@(Syn_var_decl _ _), Tk_smcl:tokens') -> let ((var_decls, expr_trees), tokens'') = parse_fun_body tokens'
                                                                                                                                 in
                                                                                                                                   ((var_decl:var_decls, expr_trees), tokens'')
                                                                           (Just var_decl@(Syn_var_decl _ _), tokens') -> let ((var_decls, expr_trees), tokens'') = parse_fun_body tokens'
                                                                                                                         in
                                                                                                                           case var_decls of
                                                                                                                             [] -> (([var_decl], expr_trees), tokens'')
                                                                                                                             -- 以下は、本来ならばassertとして検知＆停止させるべきCASE
                                                                                                                             _ -> (([var_decl], expr_trees), tokens'')
                                                                           (Just expr_par_tree, Tk_smcl:tokens') -> let ((var_decls, expr_trees), tokens'') = parse_fun_body tokens'
                                                                                                                    in
                                                                                                                      case var_decls of
                                                                                                                        [] -> (([], expr_par_tree:expr_trees), tokens'')
                                                                                                                        -- 以下は、本来ならばassertとして検知＆停止させるべきCASE
                                                                                                                        _ -> (([], expr_par_tree:expr_trees), tokens'')
                                                                           (Just expr_par_tree, tokens') -> (([], [expr_par_tree]), tokens')
                                                                           (Nothing, tokens') -> (([], []), tokens')
                                                               let fun_body' = (var_decls, (case expr_par_trees of
                                                                                              [] -> Syn_none
                                                                                              [expr] -> expr
                                                                                              exprs -> Syn_expr_seq exprs
                                                                                           )
                                                                               )
                                                               (fun', tokens') <- return (Syn_fun_decl fun_id fun_args (Syn_scope fun_body') fun_ty, us)
                                                               return $ case tokens' of
                                                                 Tk_R_bra:tokens'' -> (Just fun', tokens'')
                                                                 _ -> (Nothing, tokens')
                                                           ) of
                                                        Just res -> res
                                                        Nothing -> (Nothing, ts')
                                                     )
                       _ -> (Nothing, ts')
                    )
                  ((_, tokens'), errs) -> (Nothing, tokens')
            _:ts' -> (Nothing, ts')
          else (Nothing, ts)
        (Tk_ident ident):ts -> let var = Syn_var ident Ty_abs                                
                               in
                                 if var_declp then
                                   case cons_var_decl var ts of
                                     ((Just var_decl, tokens'), errs) -> (Just var_decl, tokens')
                                     ((Nothing, tokens'@(t:ts')), errs) | not (is_op t) -> let fun_app = Syn_expr_call ident [] Ty_abs 
                                                                                           in
                                                                                             case par_fun_call fun_app tokens' of
                                                                                               (Right (fun_app'@(Syn_expr_call fun_id app_args app_ty)), tokens'') -> cont_par fun_app' tokens''
                                                                                               (Left err, tokens'') -> (Nothing, tokens'')
                                     ((Nothing, tokens'), errs) -> cont_par var tokens'
                                 else
                                   cont_par var ts
        _ -> (Nothing, tokens)


type Fresh_tvar = (Type, Integer)

ty_abst :: (Syntree_node, Fresh_tvar) -> (Syntree_node, Fresh_tvar)
ty_abst (expr, prev_tvar) =
  (case expr of
     Syn_arg_def arg_id Ty_abs -> let latest = succ_fresh prev_tvar
                                  in
                                    (Syn_arg_def arg_id (fst latest), latest)
     Syn_var var_id Ty_abs -> let latest = succ_fresh prev_tvar
                              in
                                (Syn_var var_id (fst latest), latest)
     Syn_expr_par expr' Ty_abs -> let (expr_abs, prev_tvar') = ty_abst (expr', prev_tvar)
                                      latest = succ_fresh prev_tvar'
                                  in
                                    (Syn_expr_par expr_abs (fst latest), latest)
     Syn_expr_una ope_una expr' Ty_abs -> let (expr_abs, prev_tvar') = ty_abst (expr', prev_tvar)
                                              latest = succ_fresh prev_tvar'
                                          in
                                            (Syn_expr_una ope_una expr_abs (fst latest), latest)
     Syn_expr_bin ope_bin (expr1, expr2) Ty_abs -> let (expr1_abs, prev_tvar') = ty_abst (expr1, prev_tvar)
                                                       (expr2_abs, prev_tvar'') = ty_abst (expr2, prev_tvar')
                                                       latest = succ_fresh prev_tvar''
                                                   in
                                                     (Syn_expr_bin ope_bin (expr1_abs, expr2_abs) (fst latest), latest)
     Syn_expr_call fun_id args Ty_abs -> (case args of
                                            [] -> let latest = succ_fresh prev_tvar
                                                  in
                                                    (Syn_expr_call fun_id [] (fst latest), latest)
                                            _ -> let (args_abs, prev_tvar') = abs_args args prev_tvar
                                                     latest = succ_fresh prev_tvar'
                                                 in
                                                   (Syn_expr_call fun_id args_abs (fst latest), latest)
                                              where
                                                abs_args = abs_decls
                                         )
     Syn_cond_expr (cond_expr, (true_expr, false_expr)) Ty_abs -> let (cond_expr', prev_tvar') = ty_abst (cond_expr, prev_tvar)
                                                                      (true_expr', prev_tvar'') = ty_abst (true_expr, prev_tvar')
                                                                  in
                                                                    case false_expr of
                                                                      Just f_expr_body -> let (f_expr_body', latest) = ty_abst (f_expr_body, prev_tvar'')
                                                                                              latest' = succ_fresh latest
                                                                                          in
                                                                                            (Syn_cond_expr (cond_expr', (true_expr', Just f_expr_body')) (fst latest'), latest')
                                                                      Nothing -> let latest = succ_fresh prev_tvar''
                                                                                 in
                                                                                   (Syn_cond_expr (cond_expr', (true_expr', Nothing)) (fst latest), latest)
     Syn_fun_decl fun_id args fun_body Ty_abs  -> (case args of
                                                     [] -> let (body_abs, prev_tvar') = ty_abst (fun_body, prev_tvar)
                                                               latest = succ_fresh prev_tvar'
                                                           in
                                                             (Syn_fun_decl fun_id [] body_abs (fst latest), latest)
                                                     _ -> let (args_abs, prev_tvar') = abs_decls args prev_tvar
                                                              (body_abs, prev_tvar'') = ty_abst (fun_body, prev_tvar')
                                                              (fun_ty, latest) = abs_funty (args_abs, prev_tvar'')
                                                          in
                                                            (Syn_fun_decl fun_id args_abs body_abs fun_ty, latest)
                                                       where
                                                         abs_funty :: ([Syntree_node], Fresh_tvar) -> (Type, Fresh_tvar)
                                                         abs_funty (args, prev_tvar) =
                                                           let from_args = Prelude.foldl (\(tys, prev_tv) -> (\_ -> let prev_ty' = succ_fresh prev_tv
                                                                                                                    in
                                                                                                                      (tys ++ [(fst prev_ty')], prev_ty')
                                                                                                             )
                                                                                         ) ([], prev_tvar) args
                                                           in
                                                             case from_args of
                                                               (ty_args, prev_tvar') -> (Ty_fun (ty_args ++ [(fst latest)]), latest)
                                                                 where
                                                                   latest = succ_fresh prev_tvar'
                                                  )
     Syn_var_decl var_id Ty_abs -> let latest = succ_fresh prev_tvar
                                   in
                                     (Syn_var_decl var_id (fst latest), latest)
     Syn_expr_seq exprs -> (case exprs of
                              [] -> (Syn_expr_seq [], prev_tvar)
                              e:es -> let (e', prev_tvar') = ty_abst (e, prev_tvar)
                                          (es', latest) = abs_exprs es prev_tvar'
                                      in
                                        (Syn_expr_seq (e':es'), latest)
                                where
                                  abs_exprs = abs_decls
                           )
     Syn_scope (decls, body) -> let (decls', prev_tvar') = abs_decls decls prev_tvar
                                    (body', latest) = ty_abst (body, prev_tvar')
                                in
                                  (Syn_scope (decls', body'), latest)
     _ -> (expr, prev_tvar)
  )
  where
    first_fresh :: Fresh_tvar
    first_fresh = (Ty_var $ "t_" ++ (show 1), 1)
    succ_fresh :: Fresh_tvar -> Fresh_tvar
    succ_fresh prev =
      (Ty_var $ "t_" ++ show (last_id + 1), last_id + 1)
      where
        last_id = (snd prev)
    
    abs_decls :: [Syntree_node] -> Fresh_tvar -> ([Syntree_node], Fresh_tvar)
    abs_decls args prev_tvar =
      case args of
        [] -> ([], prev_tvar)
        a:as -> let (a', prev_tvar') = ty_abst (a, prev_tvar)
                    (as', prev_tvar'') = abs_decls as prev_tvar'
                in
                  (a':as', prev_tvar'')


data Ty_env =
  Ty_env [(String, Type)]
  deriving (Eq, Show)

expr_ty expr =
  case expr of
    Syn_expr_par _ ty -> ty
    Syn_expr_call _ _ ty -> ty
    Syn_fun_decl _ _ _ ty -> ty
    Syn_val _ ty -> ty
    Syn_var _ ty -> ty
    Syn_expr_una _ _ ty -> ty
    Syn_expr_bin _ _ ty -> ty
    _ -> Ty_unknown

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
  syn_forest <- return (do
                           syn_tree <- (case (snd tokens) of
                                           "" -> fst $ cons_par_tree (fst tokens) (True, True, True)
                                           _ -> Nothing
                                       )
                           return [syn_tree]
                       )
  putStrLn $ "p-trees: " ++ (show syn_forest)
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
