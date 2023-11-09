@testset "PolyhedralFan{$T}" for (f, T) in _prepare_scalar_types()
  C0 = cube(f, 2)
  @test normal_fan(C0) isa PolyhedralFan{T}
  NFsquare = normal_fan(C0)
  R = [1 0 0; 0 0 1]
  L = [0 1 0]
  Cone4 = positive_hull(f, R)
  Cone5 = positive_hull(f, [1 0 0; 0 1 0])

  @test polyhedral_fan([Cone4, Cone5]) isa PolyhedralFan{T}
  F0 = polyhedral_fan([Cone4, Cone5])
  I3 = [1 0 0; 0 1 0; 0 0 1]
  incidence1 = IncidenceMatrix([[1,2],[2,3]])
  incidence2 = IncidenceMatrix([[1,2]])
  @test polyhedral_fan(f, I3, incidence1) isa PolyhedralFan{T}
  F1 = polyhedral_fan(f, I3, incidence1)
  F1NR = polyhedral_fan(f, I3, incidence1; non_redundant = true)
  @test polyhedral_fan(f, I3, incidence1) isa PolyhedralFan{T}
  F2 = polyhedral_fan(f, R, L, incidence2)
  F2NR = polyhedral_fan(f, R, L, incidence2; non_redundant = true)

  @testset "core functionality" begin
    if T == QQFieldElem
      @test is_smooth(NFsquare)
    end
    @test vector_matrix(rays(NFsquare)) == matrix(f, [1 0; -1 0; 0 1; 0 -1])
    @test rays(NFsquare) isa SubObjectIterator{RayVector{T}}
    @test length(rays(NFsquare)) == 4
    @test rays(NFsquare) == [[1, 0], [-1, 0], [0, 1], [0, -1]]
    @test is_regular(NFsquare)
    @test is_complete(NFsquare)
    @test !is_complete(F0)
    @test length(rays(F0)) == 3
    @test nrays(F1) == 3
    @test dim(F1) == 2
    @test ambient_dim(F1) == 3
    @test nrays(F2) == 0
    @test lineality_dim(F2) == 1
    RMLF2 = rays_modulo_lineality(F2)
    @test length(RMLF2[:rays_modulo_lineality]) == 2
    @test maximal_cones(F1) isa SubObjectIterator{Cone{T}}
    @test dim.(maximal_cones(F1)) == [2,2]
    @test ray_indices(maximal_cones(F1)) == incidence1
    @test IncidenceMatrix(maximal_cones(F1)) == incidence1
    @test maximal_cones(IncidenceMatrix, F1) == incidence1
    @test n_maximal_cones(F1) == 2
    @test lineality_space(F2) isa SubObjectIterator{RayVector{T}}
    @test generator_matrix(lineality_space(F2)) == matrix(f, L)
    if T == QQFieldElem
      @test matrix(QQ, lineality_space(F2)) == matrix(QQ, L)
    end
    @test length(lineality_space(F2)) == 1
    @test lineality_space(F2) == [L[:]]
    @test cones(F2, 2) isa SubObjectIterator{Cone{T}}
    @test size(cones(F2, 2)) == (2,)
    @test lineality_space(cones(F2, 2)[1]) == [[0, 1, 0]]
    @test rays.(cones(F2, 2)) == [[], []]
    @test isnothing(cones(F2, 1))
    @test ray_indices(cones(F1, 2)) == incidence1
    @test IncidenceMatrix(cones(F1, 2)) == incidence1
    @test cones(IncidenceMatrix, F1, 2) == incidence1

    II = ray_indices(maximal_cones(NFsquare))
    NF0 = polyhedral_fan(rays(NFsquare), II)
    @test nrays(NF0) == 4
    FF0 = face_fan(C0)
    @test nrays(FF0) == 4
    if T == QQFieldElem
      @test !is_smooth(FF0)
    end
    @test f_vector(NFsquare) == [4, 4]
    @test rays(F1NR) == collect(eachrow(I3))
    @test ray_indices(maximal_cones(F1NR)) == incidence1
    @test IncidenceMatrix(maximal_cones(F1NR)) == incidence1
    @test nrays(F2NR) == 0
    @test lineality_dim(F2NR) == 1
    RMLF2NR = rays_modulo_lineality(F2NR)
    @test length(RMLF2NR[:rays_modulo_lineality]) == 2
    @test RMLF2NR[:rays_modulo_lineality] == collect(eachrow(R))
    @test lineality_space(F2NR) == collect(eachrow(L))
    @test ray_indices(maximal_cones(F2NR)) == incidence2
    @test IncidenceMatrix(maximal_cones(F2NR)) == incidence2

    C = positive_hull(f, identity_matrix(ZZ, 0))
    pf = polyhedral_fan(C)
    @test n_maximal_cones(pf) == 1
    @test dim(pf) == 0
    pfc = polyhedral_fan(maximal_cones(pf))
    @test n_maximal_cones(pfc) == 1

    C = positive_hull(f, vcat(identity_matrix(ZZ, 4), -identity_matrix(ZZ,4)))
    pf = polyhedral_fan(C)
    @test n_maximal_cones(pf) == 1
  end

end

@testset "Transform" for (f, T) in _prepare_scalar_types()
  square = cube(f, 2)
  nf_square = normal_fan(square)
  m_good = matrix(f, [1 0; 0 1])
  m_bad = matrix(f, [1 1])
  nf_transformed = transform(nf_square, m_good)
  @test nf_transformed isa PolyhedralFan{T}
  @test nrays(nf_transformed) == 4
  @test n_maximal_cones(nf_transformed) == 4
  @test_throws ErrorException transform(nf_square, m_bad)
  nf_unverified = transform(nf_square, m_good; check=false)
  @test nf_unverified isa PolyhedralFan{T}
  @test nrays(nf_unverified) == 4
  @test n_maximal_cones(nf_unverified) == 4

  cdeg = convex_hull(f, [1 0 0; 0 0 0])
  nflin = normal_fan(cdeg)
  mm = matrix(f, [1 0 0; 0 1 0; 0 0 1])
  nflin_transformed = transform(nflin, mm)
  @test nflin_transformed isa PolyhedralFan{T}
  @test nrays(nflin_transformed) == 0
  @test n_maximal_cones(nflin_transformed) == 2
  @test lineality_dim(nflin_transformed) == 2
end

@testset "Star Subdivision" begin
  f = polyhedral_fan([1 0 0; 1 1 0; 1 1 1; 1 0 1], IncidenceMatrix([[1,2,3,4]]))
  @test is_pure(f)
  @test is_fulldimensional(f)
  v0 = [1;0;0]
  v1 = [2;1;0]
  v2 = [2;1;1]
  sf0 = star_subdivision(f, v0)
  sf1 = star_subdivision(f, v1)
  sf2 = star_subdivision(f, v2)
  @test n_maximal_cones(sf0) == 2
  @test n_maximal_cones(sf1) == 3
  @test n_maximal_cones(sf2) == 4

  ff = polyhedral_fan([1 0 0; -1 0 0; 0 1 0], IncidenceMatrix([[1],[2,3]]))
  @test !is_pure(ff)
  @test !is_fulldimensional(ff)
  w0 = [1;0;0]
  w1 = [-1;1;0]
  sff0 = star_subdivision(ff, w0)
  sff1 = star_subdivision(ff, w1)
  @test n_maximal_cones(sff0) == 2
  @test n_maximal_cones(sff1) == 3

end
