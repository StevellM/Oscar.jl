mutable struct LineEnumCtx2{T, S}
  K::T
  a::S # primitive element
  dim::Int
  depth::Int
  v::Vector{S}
  length::BigInt
end

function LineEnumCtx2(K::T, n) where {T}
  a = Hecke.primitive_element(K)
  v = Vector{elem_type(K)}(undef, n)
  for i in 1:n
    v[i] = zero(K)
  end
  depth = n + 1
  dim = n
  q = order(K)
  length = divexact(BigInt(q)^n - 1, q - 1)
  return LineEnumCtx2{T, elem_type(T)}(K, a, dim, depth, v, length)
end

function LineEnumCtx2(K::T, n::Int) where {T <: Union{Nemo.GaloisField, Nemo.GaloisFmpzField}}
  a = zero(K)
  v = Vector{elem_type(T)}(undef, n)
  for i in 1:n
    v[i] = zero(K)
  end
  depth = n + 1
  dim = n
  q = order(K)
  length = divexact(BigInt(q)^n - 1, q - 1)
  return LineEnumCtx2{T, elem_type(T)}(K, a, dim, depth, v, length)
end

function _enumerate_lines(K, n)
  return LineEnumCtx2(K, n)
end

function Base.show(io::IO, P::LineEnumCtx2)
  print(io, "Iterator for affine lines in K^n with n = ", dim(P), "\n")
  print(io, "over ", P.K)
end

Base.length(P::LineEnumCtx2) = P.length

Base.eltype(::Type{LineEnumCtx2{T, S}}) where {T, S} = Vector{S}

depth(P::LineEnumCtx2) = P.depth

dim(P::LineEnumCtx2{T,N}) where {T,N} = P.dim

primitive_element(P::LineEnumCtx2) = P.a

function Base.getindex(P::LineEnumCtx2{T, S}, i::Union{Integer, BigInt}) where {T , S}
  @assert 1<= i<= length(P)
  K = P.K
  v = Vector{elem_type(K)}(undef, dim(P))
  for j in 1:dim(P)
    v[j] = zero(K)
  end
  if i == 1
    v[end] = one(K)
    return v
  else
    p = size(K)
    j = i-2
    n = findfirst(n -> sum(BigInt(p)^i for i=1:n) > j, 1:256)
    v[end-n] = one(K)
    j = n == 1 ? j : j-sum([BigInt(p)^k for k=1:(n-1)])
    str = base(ZZ(j), Int(p))
    for k = 1:length(str)
      v[end-length(str)+k] = K(Int(str[k])-48)
    end
    return v
  end
end

function Base.rand(P::LineEnumCtx2{T,S}) where {T , S}
  return P[Base.rand(1:length(P))]
end

function _my_rand(s, k)
  L = unique(rand(s,k))
  while length(L) < k
    unique!(append!(L, rand(s,k-length(L))))
  end
  return L
end

function neighbour(L::ZZLat, v::ZZMatrix, p::ZZRingElem)
  M = gram_matrix(L)*v
  r, K = left_kernel(matrix(GF(p), rank(L), 1, collect(M)))
  LL = lattice_in_same_ambient_space(L, lift(view(K, 1:r, :))*basis_matrix(L)) + lattice_in_same_ambient_space(L, 1//p*(transpose(v)*basis_matrix(L))) + p*L
  return LL
end

function make_admissible!(w::ZZMatrix, form::ZZMatrix, p::ZZRingElem, K::FinField)
  m = (transpose(w)*form*w)[1]
  a = mod(m, p^2)
  iszero(a) && return nothing
  a = K(div(a, p))
  v = 2*form*w
  v = map_entries(b -> K(b)//a, v)
  v = vcat(dense_matrix_type(K)[matrix(K,1,1,[one(K)]), v])
  _, L = left_kernel(v)
  @assert !iszero(view(L, :, 1))
  j = findfirst(j -> !iszero(L[j,1]), 1:nrows(L))
  @assert !isnothing(j)
  L = map_entries(b -> b//L[j,1], L)
  v = lift(L[j, 2:ncols(L)])
  for i in 1:nrows(w)
    w[i, 1] += p*v[i]
  end
  @assert iszero(mod(transpose(w)*form*w, p^2))
  return nothing
end

function neighbours_definite(L::ZZLat, p::ZZRingElem, callback, missing_mass)
  B = basis_matrix(L)
  K = GF(p)
  form = map_entries(ZZ, gram_matrix(L))

  Tp = torsion_quadratic_module(L, p*L)

  _mass = missing_mass[]

  G = gens(isometry_group(L))
  G = ZZMatrix[matrix(hom(Tp, Tp, elem_type(Tp)[Tp(lift(a)*matrix(g)) for a in gens(Tp)])) for g in G]
  G = dense_matrix_type(K)[map_entries(K, m) for m in G]
  unique!(G)
  LO = try oscar_line_orbits(matrix_group(G))
       catch e
       LO = _enumerate_lines(K, rank(L))
       end
  
  if !(LO isa LineEnumCtx2) || (length(LO) <= 300*rank(L))
    I = 1:length(LO)
  else
    I = _my_rand(1:length(LO), 300*rank(L))
  end
  result = typeof(L)[]
  @info "Lines enumerated"
  for _i in I
    w = lift(matrix(LO[_i]))
   
    a = Tp(abelian_group(Tp)(w))
    !iszero(quadratic_product(a)) && continue
    all(b -> iszero(a*b), gens(Tp)) && continue
    make_admissible!(w, form, p, K)
    LL = lll(neighbour(L, w, p))
    @hassert :ZZLatWithIsom 1 is_locally_isometric(LL, L, p)
    s = isometry_group_order(LL)
    keep, _ = callback(result, LL)
    !keep && continue
    @info "new iso class"
    _mass = _mass - 1//s
    push!(result, LL)
    if _mass == zero(fmpq)
      return result
    end
  end
  return result
end

function _mat_in_str(M::fmpq_mat)
  n,m = size(M)
  str = "matrix(QQ, $n, $m, ["
  for i=1:n
    for j= 1:m
      if M[i,j] == zero(QQ)
        str *= " 0"
      elseif denominator(M[i,j]) == 1
        str *= " $(numerator(M[i,j]))"
      else
        str *= " $(numerator(M[i,j]))//$(denominator(M[i,j]))"
      end
      if j ==m && i != n
        str *= ";"
      end
    end
  end
  str*= " ])"
  return str
end

function enumerate_lattice_in_genus(G::ZZGenus, res = ZZLat[])
  if !is_definite(G)
    return representatives(G)
  end
  if is_empty(res)
    push!(res, representative(G))
    #@info "First representative computed"
    #write(f, "reps = ZZLat[integer_lattice(;gram = $(_mat_in_str(gram_matrix(res[1])))), \n")
    #@info "Written in the file"
    L = representative(G)
    res = ZZLat[L]
    is_one(isometry_group_order(L)*mass(G)) && return res
  else
    L = res[1]
    @assert genus(L) == G
  end
  n = rank(L)
  Lq = Hecke._to_number_field_lattice(L)
  __mass = mass(G)
  K = base_field(L)
  R = base_ring(Lq)
  bps = bad_primes(G)
  p_lis = eltype(bps)[p for p in Hecke.primes_up_to(7) if !(p in bps)]
  p = Hecke._smallest_norm_good_prime(Lq)
  spinor_genera = Hecke.spinor_genera_in_genus(Lq, typeof(p)[p])
  @info "$(length(spinor_genera)) spinor genera"

  _mass = __mass
  for LL in spinor_genera
    LL = lll(Hecke._to_ZLat(LL, K = QQ))
    local found::fmpq
    found = sum(1//isometry_group_order(LL))
    found = sum(QQFieldElem[1//(isometry_group_order(LL)) for LL in res])
    missing_mass = Ref{fmpq}(_mass- found)
    new_lat = ZZLat[LL]
    while !is_zero(missing_mass[])
      @info "Try new lattice"

      callback = function(_res, M)
        keep = all(W -> !is_isometric_smart(W, M)[1], union(_res, new_lat))
        return keep, true
      end

      N = neighbours_definite(rand(res), rand(p_lis), callback, missing_mass)
      if !isempty(N)
        @hassert :ZZLatWithIsom 1 all(NN -> genus(NN) == G, N)
        found = found + sum(fmpq[1//isometry_group_order(LL) for LL in N])
        missing_mass = Ref{fmpq}(_mass-found)
        perc = Float64(found//_mass) * 100
        append!(res, N)
        append!(new_lat, N) 
        #for NN in N
        #  str = "integer_lattice(; gram = $(_mat_in_str(gram_matrix(lll(lll(NN)))))),\n"
        #  open("/home/lehrstuhl/ag-gekeler/muller/Documents/OG10-bir/gen_hard_2.jl", "a") do f
        #    write(f, str)
        #  end
        #end
        #@info "New lattices written"
        @info "Lattices: $(length(res)), Target mass: $(_mass). missing: $(missing_mass[]) ($(100-perc)%)"
      end
    end
  end
  return res
end


##############################################################################
#
#  Isometry testing
#
###############################################################################

@attr Int function absolute_kissing_number(L::ZZLat)
  is_negative_definite(L) && return kissing_number(rescale(L, -1))
  return kissing_number(L)
end

@attr QQFieldElem function extremum(L::ZZLat)
  is_negative_definite(L) && return minimum(rescale(L, -1))
  return minimum(L)
end

@attr Int function number_absolute_shortest_vectors(L::ZZLat)
  is_negative_definite(L) && return length(shortest_vectors(rescale(L, -1); check = false))
  return length(shortest_vectors(L; check = false))
end

@attr Dict{Int, Int} function numbers_absolute_short_vectors(L::ZZLat)
  LL = is_negative_definite(L) ? rescale(L, -1) : L
  D = Dict{Int, Int}()
  sv = short_vectors(LL, 0, 4)
  for i in 0:4
    D[i] = count(s[2] == i for s in sv)
  end
  return D
end

@attr MSet{Tuple{Symbol, Int}} function root_subsystem(L::ZZLat)
  return MSet(root_lattice_recognition(L)[1])
end

@attr ZZRingElem function isometry_group_order(L::ZZLat)
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
  #@req is_definite(L) && is_definite(M) "L and M must be definite"

  for func in [genus, isometry_group_order, extremum]
    func(L) != func(M) && return false
  end

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

@attr MatrixGroup{QQFieldElem,QQMatrix} function isometry_group(L::ZZLat)
  # corner case
  if rank(L) == 0
     return matrix_group(identity_matrix(QQ,degree(L)))
  end

  if !is_definite(L) && (rank(L) == 2)
    gene = automorphism_group_generators(L)
    return matrix_group([change_base_ring(QQ, m) for m in gene])
  end

  @req is_definite(L) "Lattice must be definite or of rank at most 2"

  G = gram_matrix(L)
  LL = is_negative_definite(L) ? integer_lattice(; gram = -G) : integer_lattice(; gram = G)
  gene = MagmaCall.interact() do stdout
    MagmaCall.putcmd(stdout, _to_magma_lattice(LL, "L")*"; G := AutomorphismGroup(L); Gene := Generators(G); Sprint([[[M[j,k] : k in [1..NumberOfColumns(M)]] : j in [1..NumberOfRows(M)]] : M in Gene])")
    MagmaCall.readtotoken(String, stdout, missing) |> Meta.parse |> eval
  end
  V = ambient_space(L)
  B = basis_matrix(L)
  B2 = orthogonal_complement(V, B)
  C = vcat(B, B2)
  gene = QQMatrix[block_diagonal_matrix([matrix(QQ, length(g), length(g), reduce(vcat, g)), identity_matrix(QQ, nrows(B2))]) for g in gene]
  gene = QQMatrix[inv(C)*m*C for m in gene]
  aut = matrix_group(gene)
  return aut
end

