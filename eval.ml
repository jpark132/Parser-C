open Types
open Utils

exception TypeError of string
exception DeclarationError of string
exception DivByZeroError

let rec eval_expr env e = 
   match e with 
   |Int x -> Val_Int x 
   |Bool x -> Val_Bool x      
   |Id x -> if (List.mem_assoc x env) then List.assoc x env 
         else raise(DeclarationError x)

   |Plus(exp1,exp2) -> let x = (eval_expr env exp1) in
                       let y = (eval_expr env exp2) in
                       (match (x,y) with
                           |(Val_Int c,Val_Int d) -> Val_Int (c+d)
                           |_-> raise (TypeError "one of these jaunts ain't an int"))
   |Sub(exp1,exp2) -> let x = (eval_expr env exp1) in
                      let y = (eval_expr env exp2) in
                      (match (x,y) with
                           |(Val_Int c,Val_Int d) -> Val_Int (c-d)
                           |_-> raise (TypeError "one of these jaunts ain't an int"))
   |Mult(exp1,exp2) -> let x = (eval_expr env exp1) in
                       let y = (eval_expr env exp2) in
                       (match (x,y) with
                           |(Val_Int c, Val_Int d) -> Val_Int (c*d)
                           |_-> raise (TypeError "one of these jaunts ain't an int"))
   |Div(exp1,exp2) -> let x = (eval_expr env exp1) in
                      let y = (eval_expr env exp2) in
                      (match (x,y) with 
                           |(Val_Int c, Val_Int d) -> if d = 0 then raise (DivByZeroError )
                              else Val_Int (c/d)
                           |_-> raise(TypeError "one of these jaunts ain't an int"))
   |Pow(exp1,exp2) -> let x = (eval_expr env exp1) in
                      let y = (eval_expr env exp2) in
                      (match (x,y) with
                           |(Val_Int c, Val_Int d) -> Val_Int (int_of_float (float_of_int c ** float_of_int d))
                           |_-> raise(TypeError "one of these jaunts ain't an int"))
   |Or(exp1,exp2) -> let x = (eval_expr env exp1) in
                     let y = (eval_expr env exp2) in
                     (match (x,y) with
                           |(Val_Bool c, Val_Bool d) -> Val_Bool (c || d)
                           |_-> raise(TypeError "bool or"))
   |And(exp1,exp2) -> let x = (eval_expr env exp1) in
                      let y = (eval_expr env exp2) in
                      (match (x,y) with
                           |(Val_Bool c, Val_Bool d) -> Val_Bool (c && d)
                           |_-> raise(TypeError "bool and"))
   |Not exp1 -> let x = (eval_expr env exp1) in
                (match x with 
                     |Val_Bool x -> Val_Bool (not(x))
                     |_-> raise(TypeError "bool not"))
   |Greater(exp1,exp2) -> let x = (eval_expr env exp1) in
                          let y = (eval_expr env exp2) in
                          (match (x,y) with
                              |(Val_Int c, Val_Int d) -> Val_Bool (c > d)
                              |_-> raise(TypeError "greater int"))
   |Less(exp1,exp2) -> let x = (eval_expr env exp1) in
                       let y = (eval_expr env exp2) in
                       (match (x,y) with 
                           |(Val_Int c, Val_Int d) -> Val_Bool (c < d)
                           |_-> raise(TypeError "less in"))
   |GreaterEqual(exp1,exp2) -> let x = (eval_expr env exp1) in
                               let y = (eval_expr env exp2) in
                               (match (x,y) with
                                    |(Val_Int c, Val_Int d) -> Val_Bool (c >= d)
                                    |_-> raise(TypeError "greater equal int"))
   |LessEqual(exp1,exp2) -> let x = (eval_expr env exp1) in
                            let y = (eval_expr env exp2) in
                            (match (x,y) with 
                                    |(Val_Int c, Val_Int d) -> Val_Bool (c <= d) 
                                    |_-> raise(TypeError "less equal int"))
   |Equal(exp1,exp2) -> let x = (eval_expr env exp1) in 
                        let y = (eval_expr env exp2) in
                        (match (x,y) with
                              |(Val_Int c,Val_Int d) -> Val_Bool (c = d)
                              |(Val_Bool c, Val_Bool d) -> Val_Bool (c = d)
                              |_-> raise(TypeError "equal int or bool"))
   |NotEqual(exp1,exp2) -> let x = (eval_expr env exp1) in
                           let y = (eval_expr env exp2) in
                           (match (x,y) with 
                                 |(Val_Int c, Val_Int d) -> Val_Bool (not(c = d))
                                 |(Val_Bool c, Val_Bool d) -> Val_Bool (not(c = d))
                                 |_-> raise(TypeError "notequal")) 
;;

let rec eval_stmt env s =
   match s with   
   |NoOp -> env
   |Seq(stmt1,stmt2) -> let env1 = (eval_stmt env stmt1) in
                        let env2 = (eval_stmt env1 stmt2) in
                        env2
   |Declare(d_type,id) -> if (List.mem_assoc id env) then raise(DeclarationError "already declared") else
                          if d_type = Type_Int then (id,Val_Int(0))::env
                          else (id,Val_Bool(false))::env

   |Assign(id,exp) -> if not(List.mem_assoc id env) then raise(DeclarationError "already declared") else
                      let x = (List.assoc id env) in
                      let y = (eval_expr env exp) in
                      (match x with
                      |Val_Int d -> (match y with 
                                  |Val_Int c -> let env1 = (List.remove_assoc id env) in
                                              (id,y)::env
                                  |Val_Bool c -> raise(TypeError "mismatch"))

                      |Val_Bool d -> (match y with
                                   |Val_Int c -> raise(TypeError "mismatch")
                                   |Val_Bool c -> let env1 = (List.remove_assoc id env) in
                                                (id,y)::env)
                       )

   |If(exp,stmt1,stmt2) -> let x = (eval_expr env exp) in
                           (match x with
                           |Val_Bool y -> if y = true then (eval_stmt env stmt1) else (eval_stmt env stmt2)
                           |_-> raise(TypeError "not a boolean"))

   |While(exp,stmt) -> (eval_while exp stmt env)
   |Print(exp) -> let x = (eval_expr env exp) in
                  (match x with
                  |Val_Int y ->let c = (print_output_int y) in
                               let d =(print_output_newline()) in
                               env
                  |Val_Bool y -> let c = (print_output_bool y) in
                                 let d = (print_output_newline()) in
                                 env)

and eval_while exp stmt env =
      let x = (eval_expr env exp) in
      match x with
      |Val_Bool y -> if y = true then
         let env2 = (eval_stmt env stmt) in
         (eval_while exp stmt env2)
         else
         env
      |_-> raise(TypeError "not a boolean")
;;
