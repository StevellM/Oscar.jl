@testset "spinor norms" begin
  g = ZZ[-1 0 0 0; 0 -1 0 0; 0 0 -1 0; 0 0 0 -1]
  G =  diagonal_matrix(QQFieldElem[2, 3//2, 4//3, 5//4])
  s = Oscar.spin(G, g)
  @test is_square(s//5)

  L = 2*root_lattice(:A,4)
  Oscar.sigma_sharp(L, 5)
  Oscar.sigma_sharp(L, 2)
  @test order(image_in_Oq(L)[1])==order(orthogonal_group(L))


  diag = QQ[3//2;]
  g = QQ[22876792454960;]

  @test (-1, 3) == Oscar.det_spin(diag, g, 3, 25)

  from_sage = [([2, -1, 0, -1, -2, 0, 0, 0, -10], 4, 4, 8),
 ([2, -1, 0, -1, -2, 0, 0, 0, -20], 12, 12, 24),
 ([2, 0, 0, 0, -4, 0, 0, 0, -16], 8, 8, 16),
 ([0, 0, 8, 0, -2, 0, 8, 0, 0], 8, 16, 32),
 ([-2, -1, 0, -1, -8, 0, 0, 0, 10], 12, 12, 24),
 ([2, 1, 0, 1, -2, 0, 0, 0, -40], 8, 8, 16),
 ([2, 0, 1, 0, -10, -5, 1, -5, -12], 8, 8, 16),
 ([0, 0, 10, 0, -2, -2, 10, -2, -2], 8, 8, 16),
 ([0, 0, 5, 0, -10, 0, 5, 0, 0], 120, 120, 240),
# commented some examples to speed up testing
#=([2, 0, 6, 0, -4, 0, 6, 0, -14], 16, 16, 32),
 ([0, 0, 8, 0, -4, 0, 8, 0, 8], 32, 64, 128),
 ([0, 0, 8, 0, -4, 0, 8, 0, 0], 48, 96, 192),
 ([0, 0, 12, 0, -2, 0, 12, 0, 0], 12, 24, 48),
 ([-6, 0, 0, 0, -6, 0, 0, 0, 8], 32, 32, 64),
 ([0, 0, 12, 0, -2, -2, 12, -2, 4], 8, 16, 32),
 ([-2, -1, -2, -1, 2, 9, -2, 9, -22], 16, 16, 32),
 ([0, 0, 5, 0, -12, -2, 5, -2, -2], 16, 16, 32),
 ([2, 1, 0, 1, -6, 0, 0, 0, -26], 12, 12, 24),
 ([2, 0, 0, 0, -10, 5, 0, 5, -20], 12, 12, 24),
 ([2, 0, 0, 0, -4, 0, 0, 0, -48], 16, 16, 32),
 ([2, 0, 0, 0, -16, -8, 0, -8, -16], 96, 96, 192),
 ([2, -1, 0, -1, -2, 0, 0, 0, -80], 12, 12, 24),
 ([2, 0, 0, 0, -10, 0, 0, 0, -20], 24, 24, 48),
 ([0, 0, 10, 0, -4, 0, 10, 0, 0], 48, 48, 96),
 ([0, 0, 6, 0, -12, 0, 6, 0, 0], 144, 288, 576),
 ([-2, -1, -8, -1, -8, -4, -8, -4, -2], 8, 16, 32),
 ([2, 1, 0, 1, -12, 5, 0, 5, -20], 8, 8, 16),=#
 ([0, 0, 15, 0, -2, 1, 15, 1, 2], 8, 8, 16)]

  for (g,ks,k,n) in from_sage
    g = matrix(ZZ,3,3,g)
    L = integer_lattice(gram=g)
    qL = discriminant_group(L)
    @test n == order(orthogonal_group(qL))
    @test order(image_in_Oq(L)[1]) == k
    @test order(Oscar.image_in_Oq_signed(L)[1]) == ks
  end

  L = root_lattice(:A, 7)
  k = integer_lattice(; gram = QQ[1 0 0; 0 1 0; 0 0 -1])
  L, _ direct_sum(L, k)
  GL, GLinOq = @inferred image_in_Oq(L)
  @test is_bijective(GLinOq)

  L = integer_lattice(; gram = QQ[0 1 0;1 0 0; 0 0 -3])
  GL, GLinOq = @inferred image_in_Oq_signed(L)
  @test order(GL) == 2
  @test is_bijective(GLinOq)
end

