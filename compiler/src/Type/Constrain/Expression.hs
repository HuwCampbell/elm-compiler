{-# OPTIONS_GHC -Wall #-}
module Type.Constrain.Expression
  ( constrain
  , constrainDef
  , constrainRecursiveDefs

  , TypedExpr
  , TypedDef
  , TypedDecls
  )
  where


import           Control.Arrow (first)
import           Control.Monad.Writer
import qualified Data.Map.Strict as Map
import qualified Data.Name as Name

import qualified AST.Canonical as Can
import qualified AST.Utils.Shader as Shader
import qualified Data.Index as Index
import qualified Elm.ModuleName as ModuleName
import qualified Reporting.Annotation as A
import qualified Reporting.Error.Type as E
import Reporting.Error.Type (Expected(..), Context(..), SubContext(..), MaybeName(..), Category(..), PExpected(..), PContext(..))
import qualified Type.Constrain.Pattern as Pattern
import qualified Type.Instantiate as Instantiate
import Type.Type as Type hiding (Descriptor(..))



-- CONSTRAIN


-- As we step past type annotations, the free type variables are added to
-- the "rigid type variables" dict. Allowing sharing of rigid variables
-- between nested type annotations.
--
-- So if you have a top-level type annotation like (func : a -> b) the RTV
-- dictionary will hold variables for `a` and `b`
--
type RTV =
  Map.Map Name.Name Type

type TypedExpr =
  Can.AExpr (Expected Type)

type TypedDef =
  Can.ADef (Expected Type)

type TypedDecls =
  Can.ADecls (Expected Type)

constrain :: RTV -> Can.Expr -> Expected Type -> IO (TypedExpr, Constraint)
constrain rtv expr expected =
  runWriterT $
    constrain' rtv expr expected

constrain' :: RTV -> Can.Expr -> Expected Type -> WriterT Constraint IO TypedExpr
constrain' rtv (A.At region expression) expected = do
  let at = return . A.At expected
  case expression of
    Can.VarLocal name -> do
      tell $ CLocal region name expected
      at $ Can.VarLocal name

    Can.VarTopLevel x name -> do
      tell $ CLocal region name expected
      at $ Can.VarTopLevel x name

    Can.VarKernel n0 n1 ->
      at $ Can.VarKernel n0 n1

    Can.VarForeign m0 name annotation -> do
      tell $ CForeign region name annotation expected
      at $ Can.VarForeign m0 name annotation

    Can.VarCtor ops m0 name i0 annotation -> do
      tell $ CForeign region name annotation expected
      at $ Can.VarCtor ops m0 name i0 annotation

    Can.VarDebug m0 name annotation -> do
      tell $ CForeign region name annotation expected
      at $ Can.VarDebug m0 name annotation

    Can.VarOperator op m0 n0 annotation -> do
      tell $ CForeign region op annotation expected
      at $ Can.VarOperator op m0 n0 annotation

    Can.Str s -> do
      tell $ CEqual region String Type.string expected
      at $ Can.Str s

    Can.Chr ch -> do
      tell $ CEqual region Char Type.char expected
      at $ Can.Chr ch

    Can.Int i -> do
      var <- lift mkFlexNumber
      existsW [var] $
        tell $ CEqual region E.Number (VarN var) expected
      at $ Can.Int i

    Can.Float f -> do
      tell $ CEqual region Float Type.float expected
      at $ Can.Float f

    Can.List elements ->
      constrainList rtv region elements expected

    Can.Negate expr -> do
      numberVar <- lift mkFlexNumber
      let numberType  = VarN numberVar
      existsW [numberVar] $ do
        numberExpr     <- constrain' rtv expr (FromContext region Negate numberType)
        tell            $ CEqual region E.Number numberType expected
        at $ Can.Negate numberExpr

    Can.Binop op m0 n0 annotation leftExpr rightExpr -> do
      (leftExpr1, rightExpr1) <- constrainBinop rtv region op annotation leftExpr rightExpr expected
      at $ Can.Binop op m0 n0 annotation leftExpr1 rightExpr1

    Can.Lambda args body -> do
      constrainLambda rtv region args body expected

    Can.Call func args ->
      constrainCall rtv region func args expected

    Can.If branches finally ->
      WriterT $ constrainIf rtv region branches finally expected

    Can.Case expr branches ->
      constrainCase rtv region expr branches expected

    Can.Let def body -> do
      (body', bodyC) <- lift $ constrain rtv body expected
      (def', defC) <- lift $ constrainDef rtv  def bodyC
      tell defC
      at $ Can.Let def' body'

    Can.LetRec defs body -> do
      (body', bodyC) <- lift $ constrain rtv body expected
      (defs', defC) <- lift $ constrainRecursiveDefs rtv defs bodyC
      tell defC
      at $ Can.LetRec defs' body'

    Can.LetDestruct pattern expr body -> do
      (body', bodyC) <- lift $ constrain rtv body expected
      (def', defC) <- lift $ constrainDestruct rtv region pattern expr bodyC
      tell defC
      at $ Can.LetDestruct pattern def' body'

    Can.Accessor field ->
      do  extVar <- lift mkFlexVar
          fieldVar <- lift mkFlexVar
          let extType = VarN extVar
          let fieldType = VarN fieldVar
          let recordType = RecordN (Map.singleton field fieldType) extType
          tell $ exists [ fieldVar, extVar ] $
            CEqual region (Accessor field) (FunN recordType fieldType) expected
          at (Can.Accessor field)

    Can.Access expr (A.At accessRegion field) ->
      do  extVar <- lift mkFlexVar
          fieldVar <- lift mkFlexVar
          let extType = VarN extVar
          let fieldType = VarN fieldVar
          let recordType = RecordN (Map.singleton field fieldType) extType

          let context = RecordAccess (A.toRegion expr) (getAccessName expr) accessRegion field
          existsW [ fieldVar, extVar ] $ do
            expr' <- constrain' rtv expr (FromContext region context recordType)
            tell $ CEqual region (Access field) fieldType expected
            at $ Can.Access expr' (A.At accessRegion field)

    Can.Update name expr fields ->
      constrainUpdate rtv region name expr fields expected

    Can.Record fields ->
      constrainRecord rtv region fields expected

    Can.Unit {} -> do
      tell $ CEqual region Unit UnitN expected
      at Can.Unit

    Can.Tuple a b maybeC ->
      constrainTuple rtv region a b maybeC expected

    Can.Shader src types -> WriterT $ do
      cons   <- constrainShader region types expected
      let shd = A.At expected $ Can.Shader src types
      return (shd, cons)



-- CONSTRAIN LAMBDA


constrainLambda :: RTV -> A.Region -> [Can.Pattern] -> Can.Expr -> Expected Type -> WriterT Constraint IO TypedExpr
constrainLambda rtv region args body expected =
  do  (Args vars tipe resultType (Pattern.State headers pvars revCons)) <-
        lift (constrainArgs args)

      (body0, bodyCon) <-
        lift $ constrain rtv body (NoExpectation resultType)

      tell $ exists vars $
        CAnd
          [ CLet
              { _rigidVars = []
              , _flexVars = pvars
              , _header = headers
              , _headerCon = CAnd (reverse revCons)
              , _bodyCon = bodyCon
              }
          , CEqual region Lambda tipe expected
          ]

      return $
        A.At expected $
          Can.Lambda args body0



-- CONSTRAIN CALL


constrainCall :: RTV -> A.Region -> Can.Expr -> [Can.Expr] -> Expected Type -> WriterT Constraint IO TypedExpr
constrainCall rtv region func@(A.At funcRegion _) args expected =
  do  let maybeName = getName func

      funcVar <- lift mkFlexVar
      resultVar <- lift mkFlexVar
      let funcType = VarN funcVar
      let resultType = VarN resultVar

      (funcExpr, funcCon) <- lift $ constrain rtv func (NoExpectation funcType)

      (argVars, argTypes, (argExprs, argCons)) <-
        fmap unzip . unzip3 <$> Index.indexedTraverse (fmap lift . constrainArg rtv region maybeName) args

      let arityType = foldr FunN resultType argTypes
      let category = CallResult maybeName

      tell $ exists (funcVar:resultVar:argVars) $
        CAnd
          [ funcCon
          , CEqual funcRegion category funcType (FromContext region (CallArity maybeName (length args)) arityType)
          , CAnd argCons
          , CEqual region category resultType expected
          ]

      return . A.At expected $
        Can.Call funcExpr argExprs


constrainArg :: RTV -> A.Region -> MaybeName -> Index.ZeroBased -> Can.Expr -> IO (Variable, Type, (TypedExpr, Constraint))
constrainArg rtv region maybeName index arg =
  do  argVar <- mkFlexVar
      let argType = VarN argVar
      argCon <- constrain rtv arg (FromContext region (CallArg maybeName index) argType)
      return (argVar, argType, argCon)


getName :: Can.Expr -> MaybeName
getName (A.At _ expr) =
  case expr of
    Can.VarLocal name        -> FuncName name
    Can.VarTopLevel _ name   -> FuncName name
    Can.VarForeign _ name _  -> FuncName name
    Can.VarCtor _ _ name _ _ -> CtorName name
    Can.VarOperator op _ _ _ -> OpName op
    Can.VarKernel _ name     -> FuncName name
    _                        -> NoName


getAccessName :: Can.Expr -> Maybe Name.Name
getAccessName (A.At _ expr) =
  case expr of
    Can.VarLocal name       -> Just name
    Can.VarTopLevel _ name  -> Just name
    Can.VarForeign _ name _ -> Just name
    _                       -> Nothing



-- CONSTRAIN BINOP

existsW :: [Variable] -> WriterT Constraint IO a -> WriterT Constraint IO a
existsW = censor . exists


constrainBinop :: RTV -> A.Region -> Name.Name -> Can.Annotation -> Can.Expr -> Can.Expr -> Expected Type -> WriterT Constraint IO (TypedExpr, TypedExpr)
constrainBinop rtv region op annotation leftExpr rightExpr expected =
  do  leftVar <- lift mkFlexVar
      rightVar <- lift mkFlexVar
      answerVar <- lift mkFlexVar
      let leftType = VarN leftVar
      let rightType = VarN rightVar
      let answerType = VarN answerVar
      let binopType = leftType ==> rightType ==> answerType

      existsW [ leftVar, rightVar, answerVar ] $ do
        tell $ CForeign region op annotation (NoExpectation binopType)
        tell $ CEqual region (CallResult (OpName op)) answerType expected

        leftExpr1  <- constrain' rtv leftExpr (FromContext region (OpLeft op) leftType)
        rightExpr1 <- constrain' rtv rightExpr (FromContext region (OpRight op) rightType)

        return (leftExpr1, rightExpr1)



-- CONSTRAIN LISTS


constrainList :: RTV -> A.Region -> [Can.Expr] -> Expected Type -> WriterT Constraint IO TypedExpr
constrainList rtv region entries expected =
  do  entryVar     <- lift mkFlexVar
      let entryType = VarN entryVar
      let listType  = AppN ModuleName.list Name.list [entryType]

      entryExprs <- existsW [entryVar] $ do
        tell $ CEqual region List listType expected
        Index.indexedTraverse (constrainListEntry rtv region entryType) entries

      return $ A.At expected $ Can.List entryExprs


constrainListEntry :: RTV -> A.Region -> Type -> Index.ZeroBased -> Can.Expr -> WriterT Constraint IO TypedExpr
constrainListEntry rtv region tipe index expr =
  constrain' rtv expr (FromContext region (ListEntry index) tipe)



-- CONSTRAIN IF EXPRESSIONS


constrainIf :: RTV -> A.Region -> [(Can.Expr, Can.Expr)] -> Can.Expr -> Expected Type -> IO (TypedExpr, Constraint)
constrainIf rtv region branches final expected =
  do  let boolExpect = FromContext region IfCondition Type.bool
      let (conditions, exprs) = foldr (\(c,e) (cs,es) -> (c:cs,e:es)) ([],[final]) branches

      (condExprs, condCons) <- unzip <$>
        traverse (\c -> constrain rtv c boolExpect) conditions

      case expected of
        FromAnnotation name arity _ tipe ->
          do  (branchExprs, branchCons) <-
                fmap unzip . Index.indexedForA exprs $ \index expr ->
                  constrain rtv expr (FromAnnotation name arity (TypedIfBranch index) tipe)
              let constraint =
                    CAnd
                      [ CAnd condCons
                      , CAnd branchCons
                      ]

              return (A.At expected (Can.If (zip condExprs branchExprs) (last branchExprs)), constraint)

        _ ->
          do  branchVar <- mkFlexVar
              let branchType = VarN branchVar

              (branchExprs, branchCons) <-
                fmap unzip . Index.indexedForA exprs $ \index expr ->
                  constrain rtv expr (FromContext region (IfBranch index) branchType)

              let constraint = exists [branchVar] $
                    CAnd
                      [ CAnd condCons
                      , CAnd branchCons
                      , CEqual region If branchType expected
                      ]

              return (A.At expected (Can.If (zip condExprs branchExprs) (last branchExprs)), constraint)




-- CONSTRAIN CASE EXPRESSIONS


constrainCase :: RTV -> A.Region -> Can.Expr -> [Can.CaseBranch] -> Expected Type -> WriterT Constraint IO TypedExpr
constrainCase rtv region expr branches expected =
  do  ptrnVar <- lift mkFlexVar
      let ptrnType = VarN ptrnVar

      case expected of
        FromAnnotation name arity _ tipe ->
          existsW [ptrnVar] $ do
              expr' <- constrain' rtv expr (NoExpectation ptrnType)

              branches' <- Index.indexedForA branches $ \index branch ->
                constrainCaseBranch rtv branch
                  (PFromContext region (PCaseMatch index) ptrnType)
                  (FromAnnotation name arity (TypedCaseBranch index) tipe)

              return . A.At expected $
                Can.Case expr' branches'

        _ -> do
          branchVar <- lift mkFlexVar
          let branchType = VarN branchVar
          existsW [ptrnVar, branchVar] $ do
              expr' <- constrain' rtv expr (NoExpectation ptrnType)

              branches' <- Index.indexedForA branches $ \index branch ->
                constrainCaseBranch rtv branch
                  (PFromContext region (PCaseMatch index) ptrnType)
                  (FromContext region (CaseBranch index) branchType)

              tell $ CEqual region Case branchType expected

              return . A.At expected $
                Can.Case expr' branches'



constrainCaseBranch :: RTV -> Can.CaseBranch -> PExpected Type -> Expected Type -> WriterT Constraint IO (Can.ACaseBranch (Expected Type))
constrainCaseBranch rtv (Can.CaseBranch pattern expr) pExpect bExpect =
  do  (Pattern.State headers pvars revCons) <-
        lift $ Pattern.add pattern pExpect Pattern.emptyState

      censor (CLet [] pvars headers (CAnd (reverse revCons)))
        $ Can.CaseBranch pattern <$>constrain' rtv expr bExpect



-- CONSTRAIN RECORD


constrainRecord :: RTV -> A.Region -> Map.Map Name.Name Can.Expr -> Expected Type -> WriterT Constraint IO TypedExpr
constrainRecord rtv region fields expected = WriterT $ do
    dict <- traverse (constrainField rtv) fields

    let getType (_, t, _) = t
    let recordType = RecordN (Map.map getType dict) EmptyRecordN
    let recordCon = CEqual region Record recordType expected

    let vars = Map.foldr (\(v,_,_) vs -> v:vs) [] dict
    let cons = Map.foldr (\(_,_,(_,c)) cs -> c:cs) [recordCon] dict
    let getTyped (_, _, (e,_)) = e

    let fields' = Map.map getTyped dict

    return (A.At expected (Can.Record fields'), exists vars (CAnd cons))


constrainField :: RTV -> Can.Expr -> IO (Variable, Type, (TypedExpr, Constraint))
constrainField rtv expr =
  do  var <- mkFlexVar
      let tipe = VarN var
      con <- constrain rtv expr (NoExpectation tipe)
      return (var, tipe, con)



-- CONSTRAIN RECORD UPDATE


constrainUpdate :: RTV -> A.Region -> Name.Name -> Can.Expr -> Map.Map Name.Name Can.FieldUpdate -> Expected Type -> WriterT Constraint IO TypedExpr
constrainUpdate rtv region name expr fields expected = WriterT $ do
    extVar <- mkFlexVar
    fieldDict <- Map.traverseWithKey (constrainUpdateField rtv region) fields

    recordVar <- mkFlexVar
    let recordType = VarN recordVar
    let fieldsType = RecordN (Map.map (\(_,t,_,_) -> t) fieldDict) (VarN extVar)

    -- NOTE: fieldsType is separate so that Error propagates better
    let fieldsCon = CEqual region Record recordType (NoExpectation fieldsType)
    let recordCon = CEqual region Record recordType expected

    let vars = Map.foldr (\(v,_,_,_) vs -> v:vs) [recordVar,extVar] fieldDict
    let cons = Map.foldr (\(_,_,_,c) cs -> c:cs) [recordCon] fieldDict

    (expr',con) <- constrain rtv expr (FromContext region (RecordUpdateKeys name fields) recordType)
    let getTyped (_, _, e,_) = e

    let fields' = Map.map getTyped fieldDict

    return (A.At expected (Can.Update name expr' fields'), exists vars $ CAnd (fieldsCon:con:cons))


constrainUpdateField :: RTV -> A.Region -> Name.Name -> Can.FieldUpdate -> IO (Variable, Type, Can.AFieldUpdate (Expected Type), Constraint)
constrainUpdateField rtv region field (Can.FieldUpdate fn expr) =
  do  var <- mkFlexVar
      let tipe = VarN var
      (expr', con) <- constrain rtv expr (FromContext region (RecordUpdateValue field) tipe)
      return (var, tipe, Can.FieldUpdate fn expr', con)



-- CONSTRAIN TUPLE


constrainTuple :: RTV -> A.Region -> Can.Expr -> Can.Expr -> Maybe Can.Expr -> Expected Type -> WriterT Constraint IO TypedExpr
constrainTuple rtv region a b maybeC expected =
  do  aVar <- lift mkFlexVar
      bVar <- lift mkFlexVar
      let aType = VarN aVar
      let bType = VarN bVar

      case maybeC of
        Nothing ->
          do  let tupleType = TupleN aType bType Nothing

              existsW [ aVar, bVar ] $ do
                a' <- constrain' rtv a (NoExpectation aType)
                b' <- constrain' rtv b (NoExpectation bType)
                tell $ CEqual region Tuple tupleType expected

                return . A.At expected $
                  Can.Tuple a' b' Nothing

        Just c ->
          do  cVar <- lift mkFlexVar
              let cType = VarN cVar
              let tupleType = TupleN aType bType (Just cType)

              existsW [ aVar, bVar ] $ do
                a' <- constrain' rtv a (NoExpectation aType)
                b' <- constrain' rtv b (NoExpectation bType)
                c' <- constrain' rtv c (NoExpectation cType)
                tell $ CEqual region Tuple tupleType expected
                return . A.At expected $
                  Can.Tuple a' b' (Just c')


-- CONSTRAIN SHADER


constrainShader :: A.Region -> Shader.Types -> Expected Type -> IO Constraint
constrainShader region (Shader.Types attributes uniforms varyings) expected =
  do  attrVar <- mkFlexVar
      unifVar <- mkFlexVar
      let attrType = VarN attrVar
      let unifType = VarN unifVar

      let shaderType =
            AppN ModuleName.webgl Name.shader
              [ toShaderRecord attributes attrType
              , toShaderRecord uniforms unifType
              , toShaderRecord varyings EmptyRecordN
              ]

      return $ exists [ attrVar, unifVar ] $
        CEqual region Shader shaderType expected


toShaderRecord :: Map.Map Name.Name Shader.Type -> Type -> Type
toShaderRecord types baseRecType =
  if Map.null types then
    baseRecType
  else
    RecordN (Map.map glToType types) baseRecType


glToType :: Shader.Type -> Type
glToType glType =
  case glType of
    Shader.V2 -> Type.vec2
    Shader.V3 -> Type.vec3
    Shader.V4 -> Type.vec4
    Shader.M4 -> Type.mat4
    Shader.Int -> Type.int
    Shader.Float -> Type.float
    Shader.Texture -> Type.texture



-- CONSTRAIN DESTRUCTURES


constrainDestruct :: RTV -> A.Region -> Can.Pattern -> Can.Expr -> Constraint -> IO (TypedExpr, Constraint)
constrainDestruct rtv region pattern expr bodyCon =
  do  patternVar <- mkFlexVar
      let patternType = VarN patternVar

      (Pattern.State headers pvars revCons) <-
        Pattern.add pattern (PNoExpectation patternType) Pattern.emptyState

      (expr', exprCon) <-
        constrain rtv expr (FromContext region Destructure patternType)

      let cons = CLet [] (patternVar:pvars) headers (CAnd (reverse (exprCon:revCons))) bodyCon

      return (expr', cons)


-- CONSTRAIN DEF


constrainDef :: RTV -> Can.Def -> Constraint -> IO (TypedDef, Constraint)
constrainDef rtv def bodyCon =
  case def of
    Can.Def (A.At region name) args expr ->
      do  (Args vars tipe resultType (Pattern.State headers pvars revCons)) <-
            constrainArgs args

          (expr', exprCon) <-
            constrain rtv expr (NoExpectation resultType)

          let cons =
                CLet
                  { _rigidVars = []
                  , _flexVars = vars
                  , _header = Map.singleton name (A.At region tipe)
                  , _headerCon =
                      CLet
                        { _rigidVars = []
                        , _flexVars = pvars
                        , _header = headers
                        , _headerCon = CAnd (reverse revCons)
                        , _bodyCon = exprCon
                        }
                  , _bodyCon = bodyCon
                  }

          return (Can.Def (A.At region name) args expr', cons)

    Can.TypedDef (A.At region name) freeVars typedArgs expr srcResultType ->
      do  let newNames = Map.difference freeVars rtv
          newRigids <- Map.traverseWithKey (\n _ -> nameToRigid n) newNames
          let newRtv = Map.union rtv (Map.map VarN newRigids)

          (TypedArgs tipe resultType (Pattern.State headers pvars revCons)) <-
            constrainTypedArgs newRtv name typedArgs srcResultType

          let expected = FromAnnotation name (length typedArgs) TypedBody resultType
          (expr', exprCon)  <-
            constrain newRtv expr expected

          let cons =
                CLet
                  { _rigidVars = Map.elems newRigids
                  , _flexVars = []
                  , _header = Map.singleton name (A.At region tipe)
                  , _headerCon =
                      CLet
                        { _rigidVars = []
                        , _flexVars = pvars
                        , _header = headers
                        , _headerCon = CAnd (reverse revCons)
                        , _bodyCon = exprCon
                        }
                  , _bodyCon = bodyCon
                  }

          return (Can.TypedDef (A.At region name) freeVars typedArgs expr' srcResultType, cons)



-- CONSTRAIN RECURSIVE DEFS


data Info =
  Info
    { _vars :: [Variable]
    , _cons :: [Constraint]
    , _headers :: Map.Map Name.Name (A.Located Type)
    }


{-# NOINLINE emptyInfo #-}
emptyInfo :: Info
emptyInfo =
  Info [] [] Map.empty


constrainRecursiveDefs :: RTV -> [Can.Def] -> Constraint -> IO ([TypedDef], Constraint)
constrainRecursiveDefs rtv defs bodyCon =
  recDefsHelp rtv defs bodyCon emptyInfo emptyInfo


recDefsHelp :: RTV -> [Can.Def] -> Constraint -> Info -> Info -> IO ([TypedDef], Constraint)
recDefsHelp rtv defs bodyCon rigidInfo flexInfo =
  case defs of
    [] ->
      do  let (Info rigidVars rigidCons rigidHeaders) = rigidInfo
          let (Info flexVars  flexCons  flexHeaders ) = flexInfo
          return ([],
            CLet rigidVars [] rigidHeaders CTrue $
              CLet [] flexVars flexHeaders (CLet [] [] flexHeaders CTrue (CAnd flexCons)) $
                CAnd [ CAnd rigidCons, bodyCon ]
            )

    def : otherDefs ->
      case def of
        Can.Def (A.At region name) args expr ->
          do  let (Info flexVars flexCons flexHeaders) = flexInfo

              (Args newFlexVars tipe resultType (Pattern.State headers pvars revCons)) <-
                argsHelp args (Pattern.State Map.empty flexVars [])

              (expr', exprCon) <-
                constrain rtv expr (NoExpectation resultType)

              let defCon =
                    CLet
                      { _rigidVars = []
                      , _flexVars = pvars
                      , _header = headers
                      , _headerCon = CAnd (reverse revCons)
                      , _bodyCon = exprCon
                      }

              first (Can.Def (A.At region name) args expr' :) <$>
                recDefsHelp rtv otherDefs bodyCon rigidInfo
                  ( Info
                      { _vars = newFlexVars
                      , _cons = defCon : flexCons
                      , _headers = Map.insert name (A.At region tipe) flexHeaders
                      }
                  )

        Can.TypedDef (A.At region name) freeVars typedArgs expr srcResultType ->
          do  let newNames = Map.difference freeVars rtv
              newRigids <- Map.traverseWithKey (\n _ -> nameToRigid n) newNames
              let newRtv = Map.union rtv (Map.map VarN newRigids)

              (TypedArgs tipe resultType (Pattern.State headers pvars revCons)) <-
                constrainTypedArgs newRtv name typedArgs srcResultType

              (expr', exprCon) <-
                constrain newRtv expr $
                  FromAnnotation name (length typedArgs) TypedBody resultType

              let defCon =
                    CLet
                      { _rigidVars = []
                      , _flexVars = pvars
                      , _header = headers
                      , _headerCon = CAnd (reverse revCons)
                      , _bodyCon = exprCon
                      }

              let (Info rigidVars rigidCons rigidHeaders) = rigidInfo
              first (Can.TypedDef (A.At region name) freeVars typedArgs expr' srcResultType: ) <$>
                recDefsHelp rtv otherDefs bodyCon
                  ( Info
                      { _vars = Map.foldr (:) rigidVars newRigids
                      , _cons = CLet (Map.elems newRigids) [] Map.empty defCon CTrue : rigidCons
                      , _headers = Map.insert name (A.At region tipe) rigidHeaders
                      }
                  )
                  flexInfo



-- CONSTRAIN ARGS


data Args =
  Args
    { _a_vars :: [Variable]
    , _a_type :: Type
    , _a_result :: Type
    , _a_state :: Pattern.State
    }


constrainArgs :: [Can.Pattern] -> IO Args
constrainArgs args =
  argsHelp args Pattern.emptyState


argsHelp :: [Can.Pattern] -> Pattern.State -> IO Args
argsHelp args state =
  case args of
    [] ->
      do  resultVar <- mkFlexVar
          let resultType = VarN resultVar
          return $ Args [resultVar] resultType resultType state

    pattern : otherArgs ->
      do  argVar <- mkFlexVar
          let argType = VarN argVar

          (Args vars tipe result newState) <-
            argsHelp otherArgs =<<
              Pattern.add pattern (PNoExpectation argType) state

          return (Args (argVar:vars) (FunN argType tipe) result newState)



-- CONSTRAIN TYPED ARGS


data TypedArgs =
  TypedArgs
    { _t_type :: Type
    , _t_result :: Type
    , _t_state :: Pattern.State
    }


constrainTypedArgs :: Map.Map Name.Name Type -> Name.Name -> [(Can.Pattern, Can.Type)] -> Can.Type -> IO TypedArgs
constrainTypedArgs rtv name args srcResultType =
  typedArgsHelp rtv name Index.first args srcResultType Pattern.emptyState


typedArgsHelp :: Map.Map Name.Name Type -> Name.Name -> Index.ZeroBased -> [(Can.Pattern, Can.Type)] -> Can.Type -> Pattern.State -> IO TypedArgs
typedArgsHelp rtv name index args srcResultType state =
  case args of
    [] ->
      do  resultType <- Instantiate.fromSrcType rtv srcResultType
          return $ TypedArgs resultType resultType state

    (pattern@(A.At region _), srcType) : otherArgs ->
      do  argType <- Instantiate.fromSrcType rtv srcType
          let expected = PFromContext region (PTypedArg name index) argType

          (TypedArgs tipe resultType newState) <-
            typedArgsHelp rtv name (Index.next index) otherArgs srcResultType =<<
              Pattern.add pattern expected state

          return (TypedArgs (FunN argType tipe) resultType newState)
