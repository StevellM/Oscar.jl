export defines_automorphism

@attributes TorQuadMod   # TODO: remove as soon as Hecke is patched

AutGrpAbTor = Union{AutomorphismGroup{GrpAbFinGen},AutomorphismGroup{TorQuadMod}}
AutGrpAbTorElem = Union{AutomorphismGroupElem{GrpAbFinGen},AutomorphismGroupElem{TorQuadMod}}
AbTorElem = Union{GrpAbFinGenElem,TorQuadModElem}

function _isomorphic_gap_group(A::GrpAbFinGen; T=PcGroup)
  if is_trivial(A)
    A2 = abelian_group(T, [1])
    Atop = isomorphism(PermGroup, A)
    A2top = isomorphism(PermGroup, A2)
    iso = compose(Atop, inv(A2top))
    iso2 = compose(A2top, inv(Atop))
  else
    iso = isomorphism(T, A)
    iso2 = inv(iso)
  end
  return codomain(iso), iso, iso2
end

"""
    automorphism_group(G::GrpAbFinGen) -> AutomorphismGroup{GrpAbFinGen} 

Return the automorphism group of `G`.
"""
function automorphism_group(G::GrpAbFinGen)
  Ggap, to_gap, to_oscar = _isomorphic_gap_group(G)
  AutGAP = GAP.Globals.AutomorphismGroup(Ggap.X)
  aut = AutomorphismGroup(AutGAP, G)
  set_attribute!(aut, :to_gap => to_gap, :to_oscar => to_oscar)
  return aut
end


function apply_automorphism(f::AutGrpAbTorElem, x::AbTorElem, check::Bool=true)
  aut = parent(f)
  if check
    @assert parent(x) == aut.G "Not in the domain of f!"
  end
  to_gap = get_attribute(aut, :to_gap)
  to_oscar = get_attribute(aut, :to_oscar)
  xgap = to_gap(x)
  A = parent(f)
  domGap = parent(xgap)
  imgap = typeof(xgap)(domGap, GAPWrap.Image(f.X,xgap.X))
  return to_oscar(imgap)
end
 
(f::AutGrpAbTorElem)(x::AbTorElem)  = apply_automorphism(f, x, true)
Base.:^(x::AbTorElem,f::AutGrpAbTorElem) = apply_automorphism(f, x, true)

# the _as_subgroup function needs a redefinition
# to pass on the to_gap and to_oscar attributes to the subgroup
function _as_subgroup(aut::AutomorphismGroup{S}, subgrp::GapObj) where S <: Union{TorQuadMod,GrpAbFinGen}
  function img(x::S)
    return group_element(aut, x.X)
  end
  to_gap = get_attribute(aut, :to_gap)
  to_oscar = get_attribute(aut, :to_oscar)
  subgrp1 = AutomorphismGroup{S}(subgrp, aut.G)
  set_attribute!(subgrp1, :to_gap => to_gap, :to_oscar => to_oscar)
  return subgrp1, hom(subgrp1, aut, img)
end

"""
    hom(f::AutomorphismGroupElem{GrpAbFinGen}) -> GrpAbFinGenMap 

Return the element `f` of type `GrpAbFinGenMap`.
"""
function hom(f::AutGrpAbTorElem)
  A = domain(f)
  imgs = elem_type(A)[f(a) for a in gens(A)]
  return hom(A, A, imgs)
end


function (aut::AutGrpAbTor)(f::Union{GrpAbFinGenMap,TorQuadModMor};check::Bool=true)
  !check || (domain(f) === codomain(f) === domain(aut) && is_bijective(f)) || error("Map does not define an automorphism of the abelian group.")
  to_gap = get_attribute(aut, :to_gap)
  to_oscar = get_attribute(aut, :to_oscar)
  Agap = domain(to_oscar)
  AA = Agap.X
  function img_gap(x)
    a = to_oscar(group_element(Agap,x))
    b = to_gap(f(a))
    return b.X 
  end
  gene = GAPWrap.GeneratorsOfGroup(AA)
  img = GAP.Obj([img_gap(a) for a in gene])
  fgap = GAP.Globals.GroupHomomorphismByImagesNC(AA,AA,img)
  !check || fgap in aut.X || error("Map does not define an element of the group")
  return aut(fgap)
end


function (aut::AutGrpAbTor)(M::fmpz_mat; check::Bool=true)
  !check || defines_automorphism(domain(aut),M) || error("Matrix does not define an automorphism of the abelian group.")
  return aut(hom(domain(aut),domain(aut),M); check=check)
end

function (aut::AutGrpAbTor)(g::MatrixGroupElem{fmpq, fmpq_mat}; check::Bool=true)
  L = relations(domain(aut))
  if check
    B = basis_matrix(L)
    @assert can_solve(B, B*matrix(g),side=:left)
  end
  T = domain(aut)
  g = hom(T, T, elem_type(T)[T(lift(t)*matrix(g)) for t in gens(T)])
  return aut(g)
end
"""
    matrix(f::AutomorphismGroupElem{GrpAbFinGen}) -> fmpz_mat

Return the underlying matrix of `f` as a module homomorphism.
"""
matrix(f::AutomorphismGroupElem{GrpAbFinGen}) = hom(f).map


"""
    defines_automorphism(G::GrpAbFinGen, M::fmpz_mat) -> Bool

If `M` defines an endomorphism of `G`, return `true` if `M` defines an automorphism of `G`, else `false`.
""" 
defines_automorphism(G::GrpAbFinGen, M::fmpz_mat) = is_bijective(hom(G,G,M))




################################################################################
#
#   Special functions for orthogonal groups of torsion quadratic modules
#
################################################################################


"""
    _orthogonal_group(T::TorQuadMod, gensOT::Vector{fmpz_mat}) -> AutomorphismGroup{TorQuadMod}

Return the subgroup of the orthogonal group of `G` generated by `gensOT`.
"""
function _orthogonal_group(T::TorQuadMod, gensOT::Vector{fmpz_mat}; check::Bool=true)
  Ggap, to_gap, to_oscar = _isomorphic_gap_group(abelian_group(T))
  A = abelian_group(T)
  function toA(x)
    return A(x)
  end
  function toT(x)
    return T(x)
  end
  T_to_A = Hecke.map_from_func(toA, T, A )
  A_to_T = Hecke.map_from_func(toT, A, T)
  to_oscar = compose(to_oscar, A_to_T)
  to_gap = compose(T_to_A, to_gap)
  AutGAP = GAP.Globals.AutomorphismGroup(Ggap.X)
  ambient = AutomorphismGroup(AutGAP, T)
  set_attribute!(ambient, :to_gap => to_gap, :to_oscar => to_oscar)
  gens_aut = GapObj([ambient(g, check=check).X for g in gensOT])  # performs the checks
  if check
    # expensive for large groups
    subgrp_gap =GAP.Globals.Subgroup(ambient.X, gens_aut)
  else
    subgrp_gap =GAP.Globals.SubgroupNC(ambient.X, gens_aut)
  end
  aut = AutomorphismGroup(subgrp_gap, T)
  set_attribute!(aut, :to_gap => to_gap, :to_oscar => to_oscar)
  return aut
end

function Base.show(io::IO, aut::AutomorphismGroup{TorQuadMod})
  T = domain(aut)
  print(IOContext(io, :compact => true), "Group of isometries of ", T , " generated by ", length(gens(aut)), " elements")
end


"""
    matrix(f::AutomorphismGroupElem{TorQuadMod}) -> fmpz_mat

Return a matrix inducing `f`.
"""
matrix(f::AutomorphismGroupElem{TorQuadMod}) = hom(f).map_ab.map

"""
    defines_automorphism(G::TorQuadMod, M::fmpz_mat) -> Bool

If `M` defines an endomorphism of `G`, return `true` if `M` defines an automorphism of `G`, else `false`.
"""
function defines_automorphism(G::TorQuadMod, M::fmpz_mat)
  g = hom(G, G, M)
  if !is_bijective(g)
    return false
  end
  # check that the form is preserved
  B = gens(G)
  n = length(B)
  for i in 1:n
    if Hecke.quadratic_product(B[i]) != Hecke.quadratic_product(g(B[i]))
      return false
    end
    for j in 1:i-1
      if B[i]*B[j] != g(B[i])*g(B[j])
        return false
      end
    end
  end
  return true
end

function Base.show(io::IO, ::MIME"text/plain", f::AutomorphismGroupElem{T}) where T<:TorQuadMod
  D = domain(parent(f))
  print(IOContext(io, :compact => true), "Isometry of ", D, " defined by \n")
  print(io, matrix(f))
end

function Base.show(io::IO, f::AutomorphismGroupElem{T}) where T<:TorQuadMod
  print(io, matrix(f))
end


"""
    orthogonal_group(T::TorQuadMod)  -> AutomorphismGroup{TorQuadMod}

Return the full orthogonal group of this torsion quadratic module.
"""
@attr AutomorphismGroup function orthogonal_group(T::TorQuadMod)
  # if T is not semi-regular, we want to be able to split its radical
  # quadratic. If it is not the case, we return an error since we don't
  # support this particular case.
  if !is_semi_regular(T)
    i = radical_quadratic(T)[2]
    has_complement(i)[1] || error("The radical quadratic must split")
    return _orthogonal_group_split_degenerate(T)
  end
  # if T is semi-regular, it is isometric to its normal form for which
  # we know how to compute the isometries.
  N, i = normal_form(T)
  j = inv(i)
  gensOT = _compute_gens(N)
  gensOT = TorQuadModMor[hom(N, N, g) for g in gensOT]
  gensOT = fmpz_mat[compose(compose(i,g),j).map_ab.map for g in gensOT]
  return _orthogonal_group(T, gensOT, check=false)
end

function _orthogonal_group_split_degenerate(T::TorQuadMod)
  # we need a splitting T = rd + N, where rd is the radical
  # quadratic and N is a normal form.
  #
  # If it is the case, since T splits as the sum of its primary parts,
  # then each primary part splits its radical quadratic too.
  # So, we split T into primary parts, since they don't "talk"
  # to each others via isometries, we compute the orthogonal group
  # of each primary part and we then "glue" the orthogonal groups
  # using diagonal matrices on an isometric module to T which is nice enough.
  @assert has_complement(radical_quadratic(T)[2])[1]

  # if T is "primary degenerate" then we can send it to the other function since
  # T has only one primary part.
  if is_prime_power_with_data(elementary_divisors(T)[end])[1]
    return _orthogonal_group_split_degenerate_primary(T)
  end

  # we first create some blocks corresponding to the primary parts of T.
  # We then compute the orthogonal sum of those blocks, which is a nice
  # TorQuadMod isometric to T: we get then an isometry between those two modules.
  gensOT = fmpz_mat[]
  pd = sort(prime_divisors(order(T)))
  blocks = TorQuadModMor[primary_part(T, pd[1])[2]]
  popfirst!(pd)
  while !isempty(pd)
    f = blocks[end]
    ok, j = has_complement(f)
    @assert ok
    _T = domain(j)
    _f = primary_part(_T, pd[1])[2]
    push!(blocks, compose(_f, j))
    popfirst!(pd)
  end
  Torth, _, _ = Hecke._orthogonal_sum_with_injections_and_projections(domain.(blocks))
  ok, phi = is_isometric_with_isometry(Torth, T)
  @assert ok # Same module with different basis, somehow

  # We compute the orthoognal group of each (primary) block. Since Torth is made
  # diagonally, we can generate its orthogonal group by taking some diagonal matrices
  # from taking the cartesian product on the generators of the blocks. We have nothing
  # to add since we can't map different primary parts to each others.
  orth_blocks = _orthogonal_group_split_degenerate_primary.(domain.(blocks))
  gensOTorth = fmpz_mat[]
  for x in Hecke.cartesian_product_iterator(gens.(orth_blocks), inplace=false)
    m = block_diagonal_matrix([matrix(f) for f in x])
    push!(gensOTorth, m)
  end

  gensOTorth = TorQuadModMor[hom(Torth, Torth, g) for g in gensOTorth]
  gensOT = fmpz_mat[compose(compose(inv(phi), g), phi).map_ab.map for g in gensOTorth]
  return _orthogonal_group(T, gensOT, check=false)
end

function _orthogonal_group_split_degenerate_primary(T::TorQuadMod)
  # we want only "primary" non semi regular modules that splits their
  # radical quadratic
  if is_semi_regular(T)
    return orthogonal_group(T)
  end

  @assert is_prime_power_with_data(elementary_divisors(T)[end])[1]
  rd, i = radical_quadratic(T)
  ok, j = has_complement(i)
  @assert ok
  
  # N now is isometric to a the normal form of T, so it is in particular
  # semi-regular. We can already compute generators of the orth group of
  # its normal form, we then bring them back to N
  N = domain(j)
  @assert is_semi_regular(N)
  NN, NtoNN = normal_form(N)
  @assert is_bijective(NtoNN)
  NNtoN = inv(NtoNN)
  gensONN = TorQuadModMor[hom(NN, NN, m) for m in _compute_gens(NN)]
  gensON = fmpz_mat[compose(compose(NtoNN, g), NNtoN).map_ab.map for g in gensONN]
  n1 = nrows(gensON[1])
  
  # for the rd, since its quadratic form is trivial, automorphism are just
  # automorphism of the underlying abelian group.
  gensOrd = fmpz_mat[]
  OArd = automorphism_group(abelian_group(rd))
  for f in gens(OArd)
    push!(gensOrd, matrix(f))
  end
  n2 = nrows(gensOrd[1])

  # finally, we have to consider automorphism which maps N into rd: these are well
  # defined because N and rd are orthogonal and the quadratic form on rd is trivial.
  R, psi = hom(abelian_group(N), abelian_group(rd), task = :map)
  Ntord = fmpz_mat[matrix(psi(f)) for f in gens(R)]
  Torth, _, _ = Hecke._orthogonal_sum_with_injections_and_projections([rd, N])

  # Same module with different basis
  ok, phi = is_isometric_with_isometry(Torth, T)
  @assert ok

  # We have two kind of generators: block diagonal matrices coming from isometries
  # of N and rd, and those acts identitcally on N and rd but which send N to rd.
  # Combining all of them together, we have generators (maybe the set is too big
  # compared to what is needed) for the orthogonal group of Torth, and so of T.
  gensOTorth = fmpz_mat[]
  for x in gensOrd
    m = block_diagonal_matrix([x, identity_matrix(ZZ, n1)])
    push!(gensOTorth, m)
  end
  for x in gensON
    m = block_diagonal_matrix([identity_matrix(ZZ, n2), x])
    push!(gensOTorth, m)
  end
  for m in Ntord
    M = identity_matrix(ZZ, n1+n2)
    M[(n2+1):end, 1:n2] = m
    push!(gensOTorth, M)
  end
  gensOTorth = TorQuadModMor[hom(Torth, Torth, m) for m in gensOTorth]
  gensOT = fmpz_mat[compose(compose(inv(phi), g), phi).map_ab.map for g in gensOTorth]
  return _orthogonal_group(T, gensOT, check=false)
end

