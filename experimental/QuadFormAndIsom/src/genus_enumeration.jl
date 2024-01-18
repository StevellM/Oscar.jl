function neighbour(L::ZZLat, v::ZZMatrix, p::ZZRingElem)
  M = gram_matrix(L)*v
  r, K = left_kernel(matrix(GF(p), rank(L), 1, collect(M)))
  _B = matrix(QQ, r, ncols(K), ZZRingElem[lift(ZZ, k) for k in view(K, 1:r, :)])
  LL = lattice_in_same_ambient_space(L, _B*basis_matrix(L)) + lattice_in_same_ambient_space(L, 1//p*(transpose(v)*basis_matrix(L))) + p*L
  return LL
end

function make_admissible!(w::ZZMatrix, form::ZZMatrix, p::ZZRingElem, K::FinField)
  m = only(transpose(w)*form*w)
  a = mod(m, p^2)
  iszero(a) && return nothing
  a = K(div(a, p))
  v = 2*form*w
  vK = map_entries(b -> K(b)//a, v)
  vK = reduce(vcat, dense_matrix_type(K)[identity_matrix(K, 1), vK])
  _, L = left_kernel(vK)
  @hassert :ZZLatWithIsom 3 !iszero(view(L, :, 1))
  j = findfirst(j -> !iszero(L[j, 1]), 1:nrows(L))
  @hassert :ZZLatWithIsom 3 !isnothing(j)
  L = map_entries(b -> b//L[j, 1], L)
  v = ZZRingElem[lift(ZZ, a) for a in L[j, 2:ncols(L)]]
  for i in 1:nrows(w)
    w[i, 1] += p*v[i]
  end
  @hassert :ZZLatWithIsom 3 iszero(mod(transpose(w)*form*w, p^2))
  return nothing
end

function _neighbours_definite_orbit(L::ZZLat, p::ZZRingElem; callback::Function,
                                                             inv_dict::Dict,
                                                             _invariants::Function,
                                                             save_partial::Bool = false,
                                                             save_path::Union{Nothing, String} = nothing,
                                                             use_mass::Bool = true,
                                                             missing_mass::Union{Nothing, Base.RefValue{QQFieldElem}} = nothing,
                                                             vain::Base.RefValue{Int} = Ref{Int}(0),
                                                             stop_after::IntExt = inf)
  @assert !save_partial || !isnothing(save_path)
  K = GF(p)
  form = map_entries(ZZ, gram_matrix(L))
  B = basis_matrix(L)
  Tp = torsion_quadratic_module(L, p*L)
  _, jp = radical_bilinear(Tp)

  if use_mass
    __mass = missing_mass[]
  end

  G = automorphism_group_generators(L)
  gensp = dense_matrix_type(K)[map_entries(K, solve_left(B, B*g)) for g in G]
  filter!(!is_diagonal, gensp)
  LO = Oscar.oscar_line_orbits(gensp)

  result = typeof(L)[]

  @vprintln :ZZLatWithIsom 3 "$(length(LO)) orbits of lines to try"

  for x in LO
    vain[] > stop_after && break
    w = ZZRingElem[lift(ZZ, k) for k in x]
    a = Tp(abelian_group(Tp)(w))
    if !iszero(quadratic_product(a))
      vain[] += 1
      continue
    end
    if has_preimage(jp, a)[1]
      vain[] += 1
      continue
    end

    w=matrix(ZZ, length(w), 1,w)
    make_admissible!(w, form, p, K)
    LL = lll(neighbour(L, w, p))

    @hassert :ZZLatWithIsom 3 is_locally_isometric(LL, L, p)

    keep = callback(LL)
    if !keep
      vain[] += 1
      continue
    end

    vain[] = Int(0)
    @vprintln :ZZLatWithIsom 3 "Keep an isometry class"
    invLL = _invariants(LL)
    if haskey(inv_dict, invLL)
      push!(inv_dict[invLL], LL)
    else
      inv_dict[invLL] = ZZLat[LL]
    end
    push!(result, LL)
    if save_partial
      save_partial_lattice(LL, save_path)
    end
    if use_mass
      s = automorphism_group_order(LL)
      sub!(__mass, __mass, 1//s)
      is_zero(__mass) && return result
    end
  end
  return result
end

function _neighbours_definite_rand(L::ZZLat, p::ZZRingElem; rand_neigh::Union{Nothing, Int} = nothing,
                                                            callback::Function,
                                                            inv_dict::Dict,
                                                            _invariants::Function,
                                                            save_partial::Bool = false,
                                                            save_path::Union{Nothing, String} = nothing,
                                                            use_mass::Bool = true,
                                                            missing_mass::Union{Nothing, Base.RefValue{QQFieldElem}} = nothing,
                                                            vain::Base.RefValue{Int} = Ref{Int}(0),
                                                            stop_after::IntExt = inf)
  @assert !save_partial || !isnothing(save_path)
  K = GF(p)
  form = map_entries(ZZ, gram_matrix(L))
  Tp = torsion_quadratic_module(L, p*L)
  _, jp = radical_bilinear(Tp)

  if use_mass
    __mass = missing_mass[]
  end

  P = Hecke.enumerate_lines(K, rank(L))

  result = typeof(L)[]

  maxlines = isnothing(rand_neigh) ? min(100, length(P)) : min(rand_neigh, length(P))

  @vprintln :ZZLatWithIsom 3 "Try $(maxlines) random lines"

  for i in 1:maxlines
    vain[] > stop_after && break
    w = ZZRingElem[lift(ZZ, k) for k in rand(P)]
    a = Tp(abelian_group(Tp)(w))
    if !iszero(quadratic_product(a))
      vain[] += 1
      continue
    end
    if has_preimage(jp, a)[1]
      vain[] += 1
      continue
    end
    w = matrix(ZZ, length(w), 1, w)
    make_admissible!(w, form, p, K)
    LL = lll(neighbour(L, w, p))
    @hassert :ZZLatWithIsom 3 is_locally_isometric(LL, L, p)

    keep = callback(LL)
    if !keep
      vain[] += 1
      continue
    end
    vain[] = Int(0)

    @vprintln :ZZLatWithIsom 3 "Keep an isometry class"
    invLL = _invariants(LL)
    if haskey(inv_dict, invLL)
      push!(inv_dict[invLL], LL)
    else
      inv_dict[invLL] = ZZLat[LL]
    end
    push!(result, LL)
    if save_partial
      save_partial_lattice(LL, save_path)
    end
    if use_mass
      s = automorphism_group_order(LL)
      sub!(__mass, __mass, 1//s)
      is_zero(__mass) && return result
    end
  end
  return result
end

function _unique_iso_class!(L::Vector{ZZLat})
  isempty(A) && return A
  idxs = eachindex(A)
  y = first(A)
  T = NTuple{2, Any}
  it = iterate(idxs, (iterate(idxs)::T)[2])
  count = 1
  for x in Iterators.drop(A, 1)
    if !is_isometric(x, y)
      it = it::T
      y = A[it[1]] = x
      count += 1
      it = iterate(idxs, it[2])
    end
  end
  resize!(A, count)::typeof(A)
end

# Could complement with other invariants at some point if we want
function default_func(L::ZZLat)
  m = minimum(L)
  rlr, _ = root_lattice_recognition(L)
  sort!(rlr; lt=(a,b) -> a[1] < b[1] || a[1] == b[1] && a[2] <= b[2])
  kn = kissing_number(L)::Int
  igo = automorphism_group_order(L)::ZZRingElem
  return (m, rlr, kn, igo)
end


function enumerate_definite_genus(
    known::Vector{ZZLat};
    rand_neigh::Union{Int, Nothing} = nothing,
    distinct::Bool = true,
    invariant_func::Function = default_func,
    save_partial::Bool = false,
    save_path::Union{String, Nothing} = nothing,
    use_mass::Bool = true,
    _missing_mass::Union{QQFieldElem, Nothing} = nothing,
    vain::Base.RefValue{Int} = Ref{Int}(0),
    stop_after::IntExt = inf
  )
  @req !save_partial || !isnothing(save_path) "No path mentioned for saving partial results"
  @req !is_empty(known) "Should know at least one lattice in the genus"
  @req all(LL -> genus(LL) == genus(known[1]), known) "Known lattices must be in the same genus"

  res = copy(known)
  !distinct && _unique_iso_class!(res)

  L, itk = Iterators.peel(res)
  inv_lat = invariant_func(L)
  inv_dict = Dict{typeof(inv_lat), Vector{ZZLat}}(inv_lat => ZZLat[L])
  for N in itk
    inv_lat = invariant_func(N)
    if haskey(inv_dict, inv_lat)
      push!(inv_dict[inv_lat], N)
    else
      inv_dict[inv_lat] = ZZLat[N]
    end
  end

  function _invariants(M::ZZLat)
    for (I, Z) in keys(inv_dict)
      M in Z && return I
    end
    return invariant_func(M)
  end

  callback = function(M::ZZLat)
    any(isequal(M), known) && return false
    invM = _invariants(M)
    !haskey(inv_dict, invM) && return true
    keep = all(N -> !is_isometric(N, M), inv_dict[invM])
    return keep
  end

  if use_mass
    _mass = mass(L)
    if isnothing(_missing_mass)
      found = sum(1//automorphism_group_order(M) for M in res)
      missing_mass = Ref{QQFieldElem}(_mass-found)
    else
      @hassert :ZZLatWithIsom 3 _missing_mass <= _mass
      missing_mass = Ref{QQFieldElem}(_missing_mass)
    end
  end

  ps = primes(genus(L))
  p = ZZ(3)
  while p in ps
    p = next_prime(p)
  end

  tbv = trues(length(res))
  while any(tbv)
    i = findfirst(tbv)
    tbv[i] = false
    N = try _neighbours_definite_orbit(res[i], p; callback, inv_dict, _invariants, use_mass, missing_mass, save_partial, save_path, vain, stop_after)
        catch
            _neighbours_definite_rand(res[i], p; rand_neigh, callback, inv_dict, _invariants, use_mass, missing_mass, save_partial, save_path, vain, stop_after)
        end

    if !is_empty(N)
      vain[] = 0
      for M in N
        push!(tbv, true)
        push!(res, M)
      end
      use_mass && is_zero(missing_mass[]) && break
      if use_mass
        @v_do :ZZLatWithIsom 1 perc = Float64(missing_mass[]//_mass) * 100
        @vprintln :ZZLatWithIsom 1 "Lattices: $(length(res)), Target mass: $(_mass). missing: $(missing_mass[]) ($(perc)%)"
      else
        @vprintln :ZZLatWithIsom 1 "Lattices: $(length(res))"
      end
    elseif vain[] > stop_after
      break
    end
  end
  return res, use_mass ? missing_mass[] : zero(QQ)
end

function enumerate_definite_genus(
    L::ZZLat;
    rand_neigh::Union{Int, Nothing} = nothing,
    invariant_func::Function = default_func,
    save_partial::Bool = false,
    save_path::Union{IO, String, Nothing} = nothing,
    use_mass::Bool = true,
    stop_after::IntExt = inf
  )
  @req !save_partial || !isnothing(save_path) "No path mentioned for saving partial results"

  edg = ZZLat[]
  LL = Hecke._to_number_field_lattice(L)
  p = Hecke._smallest_norm_good_prime(LL)
  spinor_genera = ZZLat[Hecke._to_ZLat(N; K=QQ) for N in Hecke.spinor_genera_in_genus(LL, typeof(p)[p])]
  @vprintln :ZZLatWithIsom 1 "$(length(spinor_genera)) spinor genera to enumerate"

  for M in spinor_genera
    vain = Ref{Int}(0)
    if use_mass
      _missing_mass = mass(M)/length(spinor_genera)
      s = automorphism_group_order(M)
      sub!(_missing_mass, _missing_mass, 1//s)
      if is_zero(_missing_mass)
        push!(edg, M)
        continue
      end
    end
    _edg, mm = enumerate_definite_genus(ZZLat[M]; rand_neigh,
                                                             invariant_func,
                                                             save_partial,
                                                             save_path,
                                                             use_mass,
                                                             _missing_mass,
                                                             vain,
                                                             stop_after)

    while use_mass && !is_zero(mm)
      vain[] > stop_after && break
      _edg, mm = enumerate_definite_genus(_edg, rand_neigh,
                                                           invariant_func,
                                                           save_partial,
                                                           save_path,
                                                           use_mass,
                                                           _missing_mass = mm,
                                                           stop_after)
    end
    append!(edg, _edg)
  end
  return edg
end

function enumerate_lattice_in_genus(G::ZZGenus)
  if !is_definite(G) || rank(G) < 3
    return representatives(G)
  else
    println(G)
    return enumerate_definite_genus(G)
  end
end

function enumerate_definite_genus(
    G::ZZGenus;
    rand_neigh::Union{Int, Nothing} = nothing,
    invariant_func::Function = default_func,
    save_partial::Bool = false,
    save_path::Union{IO, String, Nothing} = nothing,
    use_mass::Bool = true,
    stop_after::IntExt = inf
  )
  L = representative(G)
  return enumerate_definite_genus(L; rand_neigh,
                                                invariant_func,
                                                save_partial,
                                                save_path,
                                                use_mass,
                                                stop_after)
end


##############################################################################
#
#  Isometry testing
#
###############################################################################

function isometry_group_order(L::ZZLat)
  # corner case
  if rank(L) == 0
    return one(ZZ)
  end

  LL = is_negative_definite(L) ? rescale(L, -1) : L
  s = MagmaCall.interact() do stdout
    MagmaCall.putcmd(stdout, _to_magma_lattice(LL, "L")*"; G := AutomorphismGroup(L); Sprint(#G)")
    MagmaCall.readtotoken(String, stdout, missing) |> Meta.parse |> eval
  end
  return fmpz(s)
end

function is_isometric_smart(L::ZZLat, M::ZZLat)
  LL = is_negative_definite(L) ? rescale(L, -1) : L
  MM = is_negative_definite(M) ? rescale(M, -1) : M
  b = MagmaCall.interact() do stdout
    MagmaCall.putcmd(stdout, _to_magma_lattice(LL, "L")*"; "*_to_magma_lattice(MM, "M")*"; Sprint(IsIsometric(L, M))")
    MagmaCall.readtotoken(String, stdout, missing) |> Meta.parse |> eval
  end
  return b
end

function _to_magma_lattice(L::ZZLat, name::String)
  Lmat = gram_matrix(L)
  mat = "[" * split(string([Lmat[i,j] for i in 1:nrows(Lmat) for j in 1:ncols(Lmat)]), '[')[2]
  mat = replace(mat, "//" => "/")
  str = "$name := LatticeWithGram(Matrix(Rationals(), $(rank(L)), $(rank(L)), $mat))"
  return str
end

#@attr MatrixGroup{QQFieldElem,QQMatrix} function isometry_group(L::ZZLat)
#  # corner case
#  if rank(L) == 0
#     return matrix_group(identity_matrix(QQ,degree(L)))
#  end
#
#  if !is_definite(L) && (rank(L) == 2)
#    gene = automorphism_group_generators(L)
#    return matrix_group([change_base_ring(QQ, m) for m in gene])
#  end
#
#  @req is_definite(L) "Lattice must be definite or of rank at most 2"
#
#  G = gram_matrix(L)
#  LL = is_negative_definite(L) ? integer_lattice(; gram = -G) : integer_lattice(; gram = G)
#  gene = MagmaCall.interact() do stdout
#    MagmaCall.putcmd(stdout, _to_magma_lattice(LL, "L")*"; G := AutomorphismGroup(L); Gene := Generators(G); Sprint([[[M[j,k] : k in [1..NumberOfColumns(M)]] : j in [1..NumberOfRows(M)]] : M in Gene])")
#    MagmaCall.readtotoken(String, stdout, missing) |> Meta.parse |> eval
#  end
#  V = ambient_space(L)
#  B = basis_matrix(L)
#  B2 = orthogonal_complement(V, B)
#  C = vcat(B, B2)
#  gene = QQMatrix[block_diagonal_matrix([matrix(QQ, length(g), length(g), reduce(vcat, g)), identity_matrix(QQ, nrows(B2))]) for g in gene]
#  gene = QQMatrix[inv(C)*m*C for m in gene]
#  aut = matrix_group(gene)
#  return aut
#end

