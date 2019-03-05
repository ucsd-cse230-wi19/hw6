{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Hw6 where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import qualified Data.Set as S
import           Expressions 
import           Imp

--------------------------------------------------------------------------------
-- | Big-step Semantics 
--------------------------------------------------------------------------------

data BStepProp where
  BStep :: Com -> State -> State -> BStepProp 

data BStepProof where 
  BSkip   :: State -> BStepProof 
  BAssign :: Vname -> AExp -> State -> BStepProof 
  BSeq    :: Com   -> Com  -> State  -> State -> State -> BStepProof -> BStepProof -> BStepProof 
  BIfT    :: BExp  -> Com  -> Com   -> State -> State -> BStepProof -> BStepProof  
  BIfF    :: BExp  -> Com  -> Com   -> State -> State -> BStepProof -> BStepProof
  BWhileF :: BExp  -> Com  -> State -> BStepProof 
  BWhileT :: BExp  -> Com  -> State -> State -> BStepProof -> BStepProof 

{-@ data BStepProof  where 
      BSkip   :: s:State 
              -> Prop (BStep Skip s s)
    | BAssign :: x:Vname -> a:AExp -> s:State 
              -> Prop (BStep (Assign x a) s (asgn x a s)) 
    | BSeq    :: c1:Com -> c2:Com -> s1:State -> s2:State -> s3:State 
              -> Prop (BStep c1 s1 s2) -> Prop (BStep c2 s2 s3) 
              -> Prop (BStep (Seq c1 c2) s1 s3)
    | BIfT    :: b:BExp -> c1:Com -> c2:Com -> s:{State | bval b s} -> s1:State
              -> Prop (BStep c1 s s1) -> Prop (BStep (If b c1 c2) s s1)
    | BIfF    :: b:BExp -> c1:Com -> c2:Com -> s:{State | not (bval b s)} -> s2:State
              -> Prop (BStep c2 s s2) -> Prop (BStep (If b c1 c2) s s2)
    | BWhileF :: b:BExp -> c:Com -> s:{State | not (bval b s)} 
              -> Prop (BStep (While b c) s s)
    | BWhileT :: b:BExp -> c:Com -> s1:{State | bval b s1} -> s2:State
              -> Prop (BStep (Seq c (While b c)) s1 s2) 
              -> Prop (BStep (While b c) s1 s2)
  @-}  


--------------------------------------------------------------------------------
-- | Small-step Semantics 
--------------------------------------------------------------------------------

data SStepProp where
    SStep :: Com -> State -> Com -> State -> SStepProp
  
data SStepProof where
    SAssign :: Vname -> AExp -> State -> SStepProof
    SSeq1   :: Com   -> State -> SStepProof
    SSeq2   :: Com   -> Com -> Com -> State -> State -> SStepProof -> SStepProof
    SIfT    :: BExp  -> Com -> Com -> State -> SStepProof
    SIfF    :: BExp  -> Com -> Com -> State -> SStepProof
    SWhileT :: BExp  -> Com -> State -> SStepProof
    SWhileF :: BExp  -> Com -> State -> SStepProof
  
{-@ data SStepProof where
      SAssign :: x:_ -> a:_ -> s:_
              -> Prop (SStep (Assign x a) s Skip (asgn x a s))
    | SSeq1   :: c:_ -> s:_
              -> Prop (SStep (Seq Skip c) s c s)
    | SSeq2   :: c1:_ -> c1':_ -> c2:_ -> s:_ -> s':_
              -> Prop (SStep c1 s c1' s')
              -> Prop (SStep (Seq c1 c2) s  (Seq c1' c2) s')
    | SIfT    :: b:_ -> c1:_ -> c2:_ -> s:{_ | bval b s}
              -> Prop (SStep (If b c1 c2) s c1 s)
    | SIfF    :: b:_ -> c1:_ -> c2:_ -> s:{_ | not (bval b s)}
              -> Prop (SStep (If b c1 c2) s c2 s)
    | SWhileF :: b:_ -> c:_ -> s:{_ | not (bval b s)}
              -> Prop (SStep (While b c) s Skip s)
    | SWhileT :: b:_ -> c:_ -> s:{_ | (bval b s)}
              -> Prop (SStep (While b c) s (Seq c (While b c)) s)
  @-}
  
-------------------------------------------------------------------------------
-- | Zero-or-More Small Steps
-------------------------------------------------------------------------------

data SStepsProp where
  SSteps :: Com -> State -> Com -> State -> SStepsProp

data SStepsProof where
  Refl :: Com -> State -> SStepsProof
  Edge :: Com -> State -> Com -> State -> Com -> State -> SStepProof -> SStepsProof -> SStepsProof

{-@  data SStepsProof where
        Refl :: c:_ -> s:_ -> Prop (SSteps c s c s)
      | Edge :: c1:_ -> s1:_ -> c2:_ -> s2:_ -> c3:_ -> s3:_
             -> Prop (SStep c1 s1 c2 s2)
             -> Prop (SSteps c2 s2 c3 s3)
             -> Prop (SSteps c1 s1 c3 s3)
  @-}

--------------------------------------------------------------------------------
-- | Equivalence of big-step and small-step semantics: 
--   Small-Step implies Big-Step  
--------------------------------------------------------------------------------
{-@ thm_small_big :: c:_ -> s:_ -> t:_ 
      -> Prop (SSteps c s Skip t) 
      -> Prop (BStep c s t)  
  @-}
thm_small_big :: Com -> State -> State -> SStepsProof -> BStepProof 
thm_small_big _ s _ (Refl {}) 
  = BSkip s
thm_small_big c s t (Edge _ _ c' s' _ _ c_c' c'_skip) 
  = lem_small_big c s c' s' t c_c' (thm_small_big c' s' t c'_skip) 

--------------------------------------------------------------------------------
-- | Complete the hard work in the above by proving the following lemma
--------------------------------------------------------------------------------
{-@ lem_small_big :: c:_ -> s:_ -> c':_ -> s':_ -> t:_ 
               -> Prop (SStep c s c' s') 
               -> Prop (BStep c' s' t)
               -> Prop (BStep c s t) 
  @-}
--------------------------------------------------------------------------------

lem_small_big :: Com -> State -> Com -> State -> State -> SStepProof -> BStepProof -> BStepProof
lem_small_big c s c' s' t (SAssign x a _) (BSkip {}) 
  = BAssign x a s                            

lem_small_big c s _ _ t (SSeq1 c' _) s_c'_t 
  = BSeq Skip c' s s t (BSkip s) s_c'_t      

lem_small_big c s c' s' t (SSeq2 c1 c1' c2 _ _ c1_c1') (BSeq _ _ _ s'' _ c1'_s'_s'' c2_s''_t) 
  = impossible "TBD" 

lem_small_big c s c' _ t (SIfT b c1 c2 _) c1_s_t 
  = impossible "TBD"

lem_small_big c s c' s' t (SIfF b c1 c2 _) c2_s_t 
  = impossible "TBD"

lem_small_big c s c' s' t (SWhileF b cc _) (BSkip {}) 
  = impossible "TBD"

lem_small_big c s c' s' t (SWhileT b cc _) cwbc_s_t 
  = impossible "TBD"


-------------------------------------------------------------------------------
-- | Prove that if (c1, s1) goes to (c2, s2) in one step, it also does so with 
--   MANY steps (duh). 
-------------------------------------------------------------------------------
{-@ lem_ss_one :: c1:_ -> s1:_ -> c2:_ -> s2:_ 
        -> Prop (SStep c1 s1 c2 s2) 
        -> Prop (SSteps c1 s1 c2 s2) 
  @-}
lem_ss_one :: Com -> State -> Com -> State -> SStepProof -> SStepsProof 
lem_ss_one c1 s1 c2 s2 pf = impossible "TBD" 

-------------------------------------------------------------------------------
-- | The following proves that the many-steps relation is transitive ... 
-------------------------------------------------------------------------------
{-@ lem_ss_many :: c1:_ -> s1:_ -> c2:_ -> s2:_ -> c3:_ -> s3:_ 
        -> Prop (SSteps c1 s1 c2 s2) 
        -> Prop (SSteps c2 s2 c3 s3) 
        -> Prop (SSteps c1 s1 c3 s3) 
  @-}
lem_ss_many :: Com -> State -> Com -> State -> Com -> State -> SStepsProof -> SStepsProof -> SStepsProof 
lem_ss_many c1 s1 c2 s2 c3 s3 (Refl {}) rest 
  = rest 
lem_ss_many c1 s1 c2 s2 c3 s3 (Edge _ _ c1' s1' _ _ c1_c1' c1'_c2) rest 
  = Edge c1 s1 c1' s1' c3 s3 c1_c1' (lem_ss_many c1' s1' c2 s2 c3 s3 c1'_c2 rest) 

-------------------------------------------------------------------------------
-- | Prove the following helper lemma, it is a bit tricky so you can skip it 
--   for now and come back to it later. 
-------------------------------------------------------------------------------

{-@ lem_sseq2 :: c1:_ -> s1:_ -> c1':_ -> s1':_ -> c2:_ 
              -> Prop (SSteps c1 s1 c1' s1') 
              -> Prop (SSteps (Seq c1 c2) s1 (Seq c1' c2) s1') 
  @-}
lem_sseq2 :: Com -> State -> Com -> State -> Com -> SStepsProof -> SStepsProof 
lem_sseq2 c1 s1 _   _   c2 (Refl {}) 
  = impossible "TBD" 

lem_sseq2 c1 s1 c1' s1' c2 (Edge _ _ c1'' s1'' _ _ c1_c1'' c1''_c1') 
  = impossible "TBD" 

 {- INFORMAL proof of lem_sseq2 "Edge" case 

    (c1, s1) ~> (c1'', s1'')                        (c1'', s1'') ~>* (c1', s1')
    --------------------------------------[SSeq2]   ------------------------------------- [IH]
    (Seq c1 c2, s1) ~> (Seq c1'' c2, s1'')          (Seq c1'' c2, s1'') ~>* (Seq c1', s1)
    ------------------------------------------------------------------------------------- [Edge]
    (Seq c1 c2, s1) ~>* (Seq c1' c2, s1')

 -}  

--------------------------------------------------------------------------------
-- | Equivalence of big-step and small-step semantics
--   Big Step implies Small Step  
--------------------------------------------------------------------------------

{-@ thm_big_small :: c:_ -> s:_ -> t:_ -> Prop (BStep c s t) -> Prop (SSteps c s Skip t) @-}
thm_big_small :: Com -> State -> State -> BStepProof -> SStepsProof 
thm_big_small c s t (BSkip {}) 
  = Refl c s 

thm_big_small c s t (BAssign x a _) 
  = lem_ss_one c s Skip t (SAssign x a s)   

thm_big_small c s t (BWhileF cond body _) 
  = impossible "TBD" 

{- INFORMAL Proof of below case

                                           [lem_bs_ss on (c;Wbc)]
  ---------------------------[SWhileT]     ---------------------------
  (W b c, s) ~> (c; W b c, s)              (c; W b c, s) ~>* (Skip, t)
  -------------------------------------------------------------------- [Edge]
  (W b c, s)  ~>* (Skip, t)
-}
thm_big_small c s t (BWhileT cond body _s _t s_cw_s_t) 
  = Edge c s c1 s Skip t step steps 
  where 
    c1    = impossible "TBD"
    step  = impossible "TBD"
    steps = impossible "TBD"

{- INFORMAL Proof of below case

    bval b s == True                   [lem_bs_ss on c1]
    --------------------------[SIfT]   --------------------- 
    (If b c1 c2, s) ~> (c1, s)         (c1, s) ~>* (Skip, t)
    -------------------------------------------------------- [Edge]
    (If b c1 c2, s) ~>* (Skip, t)
 -}

thm_big_small c s t (BIfT b c1 c2 _ _ s_c1_t) 
  = Edge c s cmid s Skip t step steps 
  where 
    cmid  = impossible "TBD" 
    step  = impossible "TBD" 
    steps = impossible "TBD" 

{- 

    bval b s == False                  [lem_bs_ss on c1]
    --------------------------[SIfT]   --------------------- 
    (If b c1 c2, s) ~> (c2, s)         (c2, s) ~>* (Skip, t)
    -------------------------------------------------------- [Edge]
    (If b c1 c2, s) ~>* (Skip, t)

 -}

thm_big_small c s t (BIfF b c1 c2 _ _ s_c2_t) 
  = Edge c s cmid s Skip t step steps 
  where 
    cmid  = impossible "TBD" 
    step  = impossible "TBD" 
    steps = impossible "TBD" 

-- This last case is tricky, and uses `lem_sseq2`; 
-- work out an INFORMAL proof tree like the above 
-- before attempting
thm_big_small c s t (BSeq c1 c2 _ s1 _ s_c1_s1 s1_c2_t) 
  = impossible "TBD" 
 