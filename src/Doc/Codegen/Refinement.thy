theory Refinement
imports Codegen_Basics.Setup
begin

section \<open>Program and datatype refinement \label{sec:refinement}\<close>

text \<open>
  Code generation by shallow embedding (cf.~\secref{sec:principle})
  allows to choose code equations and datatype constructors freely,
  given that some very basic syntactic properties are met; this
  flexibility opens up mechanisms for refinement which allow to extend
  the scope and quality of generated code dramatically.
\<close>


subsection \<open>Program refinement\<close>

text \<open>
  Program refinement works by choosing appropriate code equations
  explicitly (cf.~\secref{sec:equations}); as example, we use Fibonacci
  numbers:
\<close>

fun %quote fib :: "nat \<Rightarrow> nat" where
    "fib 0 = 0"
  | "fib (Suc 0) = Suc 0"
  | "fib (Suc (Suc n)) = fib n + fib (Suc n)"

text \<open>
  \noindent The runtime of the corresponding code grows exponential due
  to two recursive calls:
\<close>

text %quotetypewriter \<open>
  @{code_stmts fib (consts) fib (Haskell)}
\<close>

text \<open>
  \noindent A more efficient implementation would use dynamic
  programming, e.g.~sharing of common intermediate results between
  recursive calls.  This idea is expressed by an auxiliary operation
  which computes a Fibonacci number and its successor simultaneously:
\<close>

definition %quote fib_step :: "nat \<Rightarrow> nat \<times> nat" where
  "fib_step n = (fib (Suc n), fib n)"

text \<open>
  \noindent This operation can be implemented by recursion using
  dynamic programming:
\<close>

lemma %quote [code]:
  "fib_step 0 = (Suc 0, 0)"
  "fib_step (Suc n) = (let (m, q) = fib_step n in (m + q, m))"
  by (simp_all add: fib_step_def)

text \<open>
  \noindent What remains is to implement @{const fib} by @{const
  fib_step} as follows:
\<close>

lemma %quote [code]:
  "fib 0 = 0"
  "fib (Suc n) = fst (fib_step n)"
  by (simp_all add: fib_step_def)

text \<open>
  \noindent The resulting code shows only linear growth of runtime:
\<close>

text %quotetypewriter \<open>
  @{code_stmts fib (consts) fib fib_step (Haskell)}
\<close>


subsection \<open>Datatype refinement\<close>

text \<open>
  Selecting specific code equations \emph{and} datatype constructors
  leads to datatype refinement.  As an example, we will develop an
  alternative representation of the queue example given in
  \secref{sec:queue_example}.  The amortised representation is
  convenient for generating code but exposes its \qt{implementation}
  details, which may be cumbersome when proving theorems about it.
  Therefore, here is a simple, straightforward representation of
  queues:
\<close>

datatype %quote 'a queue = Queue "'a list"

definition %quote empty :: "'a queue" where
  "empty = Queue []"

primrec %quote enqueue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "enqueue x (Queue xs) = Queue (xs @ [x])"

fun %quote dequeue :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" where
    "dequeue (Queue []) = (None, Queue [])"
  | "dequeue (Queue (x # xs)) = (Some x, Queue xs)"

text \<open>
  \noindent This we can use directly for proving;  for executing,
  we provide an alternative characterisation:
\<close>

definition %quote AQueue :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a queue" where
  "AQueue xs ys = Queue (ys @ rev xs)"

code_datatype %quote AQueue

text \<open>
  \noindent Here we define a \qt{constructor} @{const "AQueue"} which
  is defined in terms of @{text "Queue"} and interprets its arguments
  according to what the \emph{content} of an amortised queue is supposed
  to be.

  The prerequisite for datatype constructors is only syntactical: a
  constructor must be of type @{text "\<tau> = \<dots> \<Rightarrow> \<kappa> \<alpha>\<^sub>1 \<dots> \<alpha>\<^sub>n"} where @{text
  "{\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n}"} is exactly the set of \emph{all} type variables in
  @{text "\<tau>"}; then @{text "\<kappa>"} is its corresponding datatype.  The
  HOL datatype package by default registers any new datatype with its
  constructors, but this may be changed using @{command_def
  code_datatype}; the currently chosen constructors can be inspected
  using the @{command print_codesetup} command.

  Equipped with this, we are able to prove the following equations
  for our primitive queue operations which \qt{implement} the simple
  queues in an amortised fashion:
\<close>

lemma %quote empty_AQueue [code]:
  "empty = AQueue [] []"
  by (simp add: AQueue_def empty_def)

lemma %quote enqueue_AQueue [code]:
  "enqueue x (AQueue xs ys) = AQueue (x # xs) ys"
  by (simp add: AQueue_def)

lemma %quote dequeue_AQueue [code]:
  "dequeue (AQueue xs []) =
    (if xs = [] then (None, AQueue [] [])
    else dequeue (AQueue [] (rev xs)))"
  "dequeue (AQueue xs (y # ys)) = (Some y, AQueue xs ys)"
  by (simp_all add: AQueue_def)

text \<open>
  \noindent It is good style, although no absolute requirement, to
  provide code equations for the original artefacts of the implemented
  type, if possible; in our case, these are the datatype constructor
  @{const Queue} and the case combinator @{const case_queue}:
\<close>

lemma %quote Queue_AQueue [code]:
  "Queue = AQueue []"
  by (simp add: AQueue_def fun_eq_iff)

lemma %quote case_queue_AQueue [code]:
  "case_queue f (AQueue xs ys) = f (ys @ rev xs)"
  by (simp add: AQueue_def)

text \<open>
  \noindent The resulting code looks as expected:
\<close>

text %quotetypewriter \<open>
  @{code_stmts empty enqueue dequeue Queue case_queue (SML)}
\<close>

text \<open>
  The same techniques can also be applied to types which are not
  specified as datatypes, e.g.~type @{typ int} is originally specified
  as quotient type by means of @{command_def typedef}, but for code
  generation constants allowing construction of binary numeral values
  are used as constructors for @{typ int}.

  This approach however fails if the representation of a type demands
  invariants; this issue is discussed in the next section.
\<close>


subsection \<open>Datatype refinement involving invariants \label{sec:invariant}\<close>

text \<open>
  Datatype representation involving invariants require a dedicated
  setup for the type and its primitive operations.  As a running
  example, we implement a type @{typ "'a dlist"} of lists consisting
  of distinct elements.

  The specification of @{typ "'a dlist"} itself can be found in theory
  @{theory "HOL-Library.Dlist"}.

  The first step is to decide on which representation the abstract
  type (in our example @{typ "'a dlist"}) should be implemented.
  Here we choose @{typ "'a list"}.  Then a conversion from the concrete
  type to the abstract type must be specified, here:
\<close>

text %quote \<open>
  @{term_type Dlist}
\<close>

text \<open>
  \noindent Next follows the specification of a suitable \emph{projection},
  i.e.~a conversion from abstract to concrete type:
\<close>

text %quote \<open>
  @{term_type list_of_dlist}
\<close>

text \<open>
  \noindent This projection must be specified such that the following
  \emph{abstract datatype certificate} can be proven:
\<close>

lemma %quote [code abstype]:
  "Dlist (list_of_dlist dxs) = dxs"
  by (fact Dlist_list_of_dlist)

text \<open>
  \noindent Note that so far the invariant on representations
  (@{term_type distinct}) has never been mentioned explicitly:
  the invariant is only referred to implicitly: all values in
  set @{term "{xs. list_of_dlist (Dlist xs) = xs}"} are invariant,
  and in our example this is exactly @{term "{xs. distinct xs}"}.
  
  The primitive operations on @{typ "'a dlist"} are specified
  indirectly using the projection @{const list_of_dlist}.  For
  the empty @{text "dlist"}, @{const Dlist.empty}, we finally want
  the code equation
\<close>

text %quote \<open>
  @{term "Dlist.empty = Dlist []"}
\<close>

text \<open>
  \noindent This we have to prove indirectly as follows:
\<close>

lemma %quote [code]:
  "list_of_dlist Dlist.empty = []"
  by (fact list_of_dlist_empty)

text \<open>
  \noindent This equation logically encodes both the desired code
  equation and that the expression @{const Dlist} is applied to obeys
  the implicit invariant.  Equations for insertion and removal are
  similar:
\<close>

lemma %quote [code]:
  "list_of_dlist (Dlist.insert x dxs) = List.insert x (list_of_dlist dxs)"
  by (fact list_of_dlist_insert)

lemma %quote [code]:
  "list_of_dlist (Dlist.remove x dxs) = remove1 x (list_of_dlist dxs)"
  by (fact list_of_dlist_remove)

text \<open>
  \noindent Then the corresponding code is as follows:
\<close>

text %quotetypewriter \<open>
  @{code_stmts Dlist.empty Dlist.insert Dlist.remove list_of_dlist (Haskell)}
\<close>

text \<open>
  See further @{cite "Haftmann-Kraus-Kuncar-Nipkow:2013:data_refinement"}
  for the meta theory of datatype refinement involving invariants.

  Typical data structures implemented by representations involving
  invariants are available in the library, theory @{theory "HOL-Library.Mapping"}
  specifies key-value-mappings (type @{typ "('a, 'b) mapping"});
  these can be implemented by red-black-trees (theory @{theory "HOL-Library.RBT"}).
\<close>

end
