(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)

(** S-Expressions over string atoms

    @author Christoph Sticksel 

*)


(** Define the type of the result from the functor application *)
module type StringSExpr = SExprBase.S with type atom = string

(** Include the module here to avoid having to write
    [StringSExpr.StringSExpr] *)
include StringSExpr


(* 
   Local Variables:
   indent-tabs-mode: nil
   End: 
*)
