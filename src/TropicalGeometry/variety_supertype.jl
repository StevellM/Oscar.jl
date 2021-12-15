###
# Tropical variety supertype in Oscar (not for public use)
# ===================================
###


###
# 0. Definition
# -------------
# M = typeof(min) or typeof(max):
#   min or max convention
# EMB = true or false:
#   embedded or abstract
# see also: variety.jl, hypersurface.jl, curve.jl, linear_space.jl
###

abstract type TropicalVarietySupertype{M,EMB} end
function pm_object(v::TropicalVarietySupertype)
  return v.polymakeTV
end


###
# 1. Basic constructions
# ----------------------
###

@doc Markdown.doc"""
    intersect(TV1, TV2)

Intersect two tropical varieties.

# Examples
```jldoctest
julia> T = tropical_numbers(min)
Tropical ring (min)

julia> Txy,(x,y) = T["x","y"]
(Multivariate Polynomial Ring in x, y over Tropical ring (min), AbstractAlgebra.Generic.MPoly{Oscar.TropicalNumbersElem{typeof(min)}}[x, y])

julia> f1 = x+y+1
x + y + (1)

julia> f2 = x^2+y^2+T(-6)
x^2 + y^2 + (-6)

julia> hyp1 = TropicalHypersurface(f1)
A min tropical hypersurface embedded in 2-dimensional Euclidian space

julia> hyp2 = TropicalHypersurface(f2)
A min tropical hypersurface embedded in 2-dimensional Euclidian space

julia> tv12 = intersect(hyp1, hyp2)
A min tropical variety of dimension 1 embedded in 2-dimensional Euclidian space
```
"""
function intersect(TV1::TropicalVarietySupertype{M, EMB}, TV2::TropicalVarietySupertype{M, EMB}) where {M, EMB}
    pm_tv1 = pm_object(TV1)
    pm_tv2 = pm_object(TV2)
    result = Polymake.fan.PolyhedralComplex(Polymake.fan.common_refinement(pm_tv1, pm_tv2))
    result = polyhedral_complex_workaround(result)
    return TropicalVariety{M, EMB}(result)
end


@doc Markdown.doc"""
    stably_intersect(TV1, TV2)

# Examples
```jldoctest
```
"""
function stably_intersect(TV1::TropicalVarietySupertype{M, EMB}, TV2::TropicalVarietySupertype{M, EMB}) where {M, EMB}
    pm_tv1 = pm_object(TV1)
    pm_tv2 = pm_object(TV2)
    result = Polymake.fan.common_refinement(pm_tv1, pm_tv2)
    k = dim(TV1) + dim(TV2) - ambient_dim(TV1)
    result = Polymake.fan.PolyhedralComplex(Polymake.fan.k_skeleton(result, k+1))
    result = polyhedral_complex_workaround(result)
    return TropicalVariety{M, EMB}(result)
end
export stably_intersect



###
# 2. Basic properties
# -------------------
###

@doc Markdown.doc"""
    ambient_dim(TV::TropicalVariety{M, EMB})
    ambient_dim(TV::TropicalCurve{M, EMB})
    ambient_dim(TV::TropicalHypersurface{M, EMB})
    ambient_dim(TV::TropicalLinearSpace{M, EMB})

Returns the ambient dimension of `TV` if it is embedded. Returns an error otherwise.

# Examples
A tropical hypersurface in RR^n is of ambient dimension n
```jldoctest
julia> T = tropical_numbers(min);

julia> Txy,(x,y) = T["x","y"];

julia> f = x+y+1;

julia> tropicalLine = TropicalHypersurface(f);

julia> ambient_dim(tropicalLine)
# todo: add examples for varieties, curves and linear spaces
```
"""
function ambient_dim(TV::TropicalVarietySupertype{M,EMB}) where {M,EMB}
    if !EMB
        error("ambient_dim: tropical variety not embedded")
    end

    return pm_object(TV).FAN_AMBIENT_DIM-2 # todo: is this the property to use?
end



@doc Markdown.doc"""
    dim(TV::TropicalVariety{M, EMB})
    dim(TV::TropicalCurve{M, EMB})
    dim(TV::TropicalHypersurface{M, EMB})
    dim(TV::TropicalLinearSpace{M, EMB})

Returns the dimension of `TV`.

# Examples
A tropical hypersurface in RR^n is always of dimension n-1
```jldoctest
julia> T = tropical_numbers(min);

julia> Txy,(x,y) = T["x","y"];

julia> f = x+y+1;

julia> tropicalLine = TropicalHypersurface(f);

julia> dim(tropicalLine)
# todo: add examples for varieties, curves and linear spaces
```
"""
dim(TV::TropicalVarietySupertype{M,EMB}) where {M, EMB} = pm_object(TV).FAN_DIM-1



@doc Markdown.doc"""
    f_vector(TV::TropicalVariety{M, EMB})
    f_vector(TV::TropicalCurve{M, EMB})
    f_vector(TV::TropicalHypersurface{M, EMB})
    f_vector(TV::TropicalLinearSpace{M, EMB})

Returns the f-Vector of `TV`.

# Examples
A tropical hypersurface in RR^n is of lineality dimension n
```jldoctest
julia> T = tropical_numbers(min);

julia> Txy,(x,y) = T["x","y"];

julia> f = x+y+1;

julia> tropicalLine = TropicalHypersurface(f);

julia> f_vector(tropicalLine)
# todo: add examples for varieties, curves and linear spaces
```
"""
function f_vector(TV::TropicalVarietySupertype{M,EMB}) where {M,EMB}
    pmtv = pm_object(TV)
    ldim = pmtv.LINEALITY_DIM
    return vcat(fill(0,ldim),pmtv.F_VECTOR)
end



@doc Markdown.doc"""
    lineality_dim(TV::TropicalVariety{M, EMB})
    lineality_dim(TV::TropicalCurve{M, EMB})
    lineality_dim(TV::TropicalHypersurface{M, EMB})
    lineality_dim(TV::TropicalLinearSpace{M, EMB})

Returns the dimension of the lineality space of `TV` if it is embedded. Returns an error otherwise.

# Examples
A tropical hypersurface in RR^n is of lineality dimension n
```jldoctest
julia> T = tropical_numbers(min);

julia> Txy,(x,y) = T["x","y"];

julia> f = x+y;

julia> tropicalAndAffineLine = TropicalHypersurface(f);

julia> lineality_dim(tropicalAndAffineLine)
# todo: add examples for varieties, curves and linear spaces
```
"""
function lineality_dim(TV::TropicalVarietySupertype{M,EMB}) where {M,EMB}
    if !EMB
        error("lineality_dim: tropical variety not embedded")
    end

    return pm_object(TV).LINEALITY_DIM
end



@doc Markdown.doc"""
    lineality_space(TV::TropicalVariety{M, EMB})
    lineality_space(TV::TropicalCurve{M, EMB})
    lineality_space(TV::TropicalHypersurface{M, EMB})
    lineality_space(TV::TropicalLinearSpace{M, EMB})

Returns the lineality space of `TV` if it is embedded. Returns an error otherwise.

# Examples
A tropical hypersurface in RR^n is of lineality spaceension n
```jldoctest
julia> T = tropical_numbers(min);

julia> Txy,(x,y) = T["x","y"];

julia> f = x+y;

julia> tropicalAndAffineLine = TropicalHypersurface(f);

julia> lineality_space(tropicalAndAffineLine)
# todo: add examples for varieties, curves and linear spaces
```
"""
function lineality_space(TV::TropicalVarietySupertype{M,EMB}) where {M,EMB}
    if !EMB
        error("lineality_space: tropical variety not embedded")
    end

    return SubObjectIterator{RayVector{Polymake.Rational}}(pm_object(TV), _lineality_fan, lineality_dim(TV))
end # todo: this returns the wrong answer (no lineality in the example above)



@doc Markdown.doc"""
    maximal_polyhedra(TV::TropicalVariety{M, EMB})
    maximal_polyhedra(TV::TropicalCurve{M, EMB})
    maximal_polyhedra(TV::TropicalHypersurface{M, EMB})
    maximal_polyhedra(TV::TropicalLinearSpace{M, EMB})

Returns the maximal polyhedra of `TV`.

# Examples
A tropical hypersurface in RR^n is of lineality dimension n
```jldoctest
julia> T = tropical_numbers(min);

julia> Txy,(x,y) = T["x","y"];

julia> f = x+y+1;

julia> tropicalLine = TropicalHypersurface(f);

julia> maximal_polyhedra(tropicalLine)
# todo: add examples for varieties, curves and linear spaces
```
"""
function maximal_polyhedra(TV::TropicalVarietySupertype{M,EMB}) where {M,EMB}
    # TODO!!!
end



@doc Markdown.doc"""
    n_maximal_polyhedra(TV::TropicalVariety{M, EMB})
    n_maximal_polyhedra(TV::TropicalCurve{M, EMB})
    n_maximal_polyhedra(TV::TropicalHypersurface{M, EMB})
    n_maximal_polyhedra(TV::TropicalLinearSpace{M, EMB})

Returns the number of maximal polyhedra of `TV`.

# Examples
A tropical hypersurface in RR^n is of lineality dimension n
```jldoctest
julia> T = tropical_numbers(min);

julia> Txy,(x,y) = T["x","y"];

julia> f = x+y+1;

julia> tropicalLine = TropicalHypersurface(f);

julia> n_maximal_polyhedra(tropicalLine)
# todo: add examples for varieties, curves and linear spaces
# todo: do maximal polyhedra at infinity count?
```
"""
function n_maximal_polyhedra(TV::TropicalVarietySupertype{M,EMB}) where {M,EMB}
    return pm_object(TV).N_MAXIMAL_POLYTOPES
end



@doc Markdown.doc"""
    n_polyhedra(TV::TropicalVariety{M, EMB})
    n_polyhedra(TV::TropicalCurve{M, EMB})
    n_polyhedra(TV::TropicalHypersurface{M, EMB})
    n_polyhedra(TV::TropicalLinearSpace{M, EMB})

Returns the number of polyhedra of `TV`.

# Examples
A tropical hypersurface in RR^n is of lineality dimension n
```jldoctest
julia> T = tropical_numbers(min);

julia> Txy,(x,y) = T["x","y"];

julia> f = x+y+1;

julia> tropicalLine = TropicalHypersurface(f);

julia> n_polyhedra(tropicalLine)
# todo: add examples for varieties, curves and linear spaces
# todo: do polyhedra at infinity count?
```
"""
function n_polyhedra(TV::TropicalVarietySupertype{M,EMB}) where {M,EMB}
    return pm_object(TV).N_POLYTOPES
end



@doc Markdown.doc"""
    n_vertices(TV::TropicalVariety{M, EMB})
    n_vertices(TV::TropicalCurve{M, EMB})
    n_vertices(TV::TropicalHypersurface{M, EMB})
    n_vertices(TV::TropicalLinearSpace{M, EMB})

Returns the number of vertices of `TV`.

# Examples
A tropical hypersurface in RR^n is of lineality dimension n
```jldoctest
julia> T = tropical_numbers(min);

julia> Txy,(x,y) = T["x","y"];

julia> f = x+y+1;

julia> tropicalLine = TropicalHypersurface(f);

julia> n_vertices(tropicalLine)
# todo: add examples for varieties, curves and linear spaces
# todo: do vertices at infinity count?
```
"""
function n_vertices(TV::TropicalVarietySupertype{M,EMB}) where {M,EMB}
    return pm_object(TV).N_VERTICES
end



@doc Markdown.doc"""
    polyhedra(TV::TropicalVariety{M, EMB})
    polyhedra(TV::TropicalCurve{M, EMB})
    polyhedra(TV::TropicalHypersurface{M, EMB})
    polyhedra(TV::TropicalLinearSpace{M, EMB})

Returns the polyhedra of `TV`.

# Examples
A tropical hypersurface in RR^n is of lineality dimension n
```jldoctest
julia> T = tropical_numbers(min);

julia> Txy,(x,y) = T["x","y"];

julia> f = x+y+1;

julia> tropicalLine = TropicalHypersurface(f);

julia> polyhedra(tropicalLine)
# todo: add examples for varieties, curves and linear spaces
# todo: do vertices at infinity count?
```
"""
function polyhedra(TV::TropicalVarietySupertype{M,EMB}) where {M,EMB}
    # TODO!!!
end



@doc Markdown.doc"""
    pure(TV::TropicalVariety{M, EMB})
    pure(TV::TropicalCurve{M, EMB})
    pure(TV::TropicalHypersurface{M, EMB})
    pure(TV::TropicalLinearSpace{M, EMB})

Return true if `TV` is a pure polyhedral complex, false otherwise.

# Examples
A tropical hypersurface in RR^n is of lineality dimension n
```jldoctest
julia> T = tropical_numbers(min);

julia> Txy,(x,y) = T["x","y"];

julia> f = x+y+1;

julia> tropicalLine = TropicalHypersurface(f);

julia> pure(tropicalLine)
# todo: add examples for varieties, curves and linear spaces
```
"""
function pure(TV::TropicalVarietySupertype{M,EMB}) where {M,EMB}
    return pm_object(TV).PURE
end



@doc Markdown.doc"""
    simplicial(TV::TropicalVariety{M, EMB})
    simplicial(TV::TropicalCurve{M, EMB})
    simplicial(TV::TropicalHypersurface{M, EMB})
    simplicial(TV::TropicalLinearSpace{M, EMB})

Returns true if `TV` is a simplicial polyhedral complex, false otherwise.

# Examples
A tropical hypersurface in RR^n is of lineality dimension n
```jldoctest
julia> T = tropical_numbers(min);

julia> Txy,(x,y) = T["x","y"];

julia> f = x+y+1;

julia> tropicalLine = TropicalHypersurface(f);

julia> simplicial(tropicalLine)
# todo: add examples for varieties, curves and linear spaces
```
"""
function simplicial(TV::TropicalVarietySupertype{M,EMB}) where {M,EMB}
    return pm_object(TV).SIMPLICIAL
end



@doc Markdown.doc"""
    vertices(TV::TropicalVariety{M, EMB})
    vertices(TV::TropicalCurve{M, EMB})
    vertices(TV::TropicalHypersurface{M, EMB})
    vertices(TV::TropicalLinearSpace{M, EMB})

Returns the vertices of `TV`, which are points in euclidean space if TV is embedded or elements in an ordered set otherwise.

# Examples
The vertices of a plane tropical line, plane tropical honeycomb quadric, and plane tropical honeycomb cubic
```jldoctest
julia> T = tropical_numbers(min);

julia> Txy,(x,y) = T["x","y"];

julia> f1 = x+y+1;

julia> tropicalLine = TropicalHypersurface(f1);

julia> vertices(tropicalLine)

julia> f2 = 1*x^2+x*y+1*y^2+x+y+1;

julia> tropicalQuadric = TropicalHypersurface(f1);

julia> vertices(tropicalQuadric)

julia> f3 = x^3+x*y^2+x^2*y+y^3+x^2+x*y+y^2+x+y+1;

julia> tropicalCubic = TropicalHypersurface(f3);

julia> vertices(tropicalCubic)
```
"""
function vertices(as::Type{PointVector{T}}, TV::TropicalVarietySupertype{M,EMB}) where {T,M,EMB}
    pmtv = pm_object(TV)
    return SubObjectIterator{as}(pmtv, _vertex_polyhedron, length(_vertex_indices(pmtv)))
end

vertices(TV::TropicalVarietySupertype{M, EMB}) where {M,EMB} = vertices(PointVector, TV)

vertices(PointVector, TV::TropicalVarietySupertype{M, EMB}) where {T,M,EMB} = vertices(PointVector{Polymake.Rational}, TV)



@doc Markdown.doc"""
    weights(TV::TropicalVariety{M, EMB})
    weights(TV::TropicalCurve{M, EMB})
    weights(TV::TropicalHypersurface{M, EMB})
    weights(TV::TropicalLinearSpace{M, EMB})

Returns the weights of `TV`.

# Examples
A tropical hypersurface in RR^n is of lineality dimension n
```jldoctest
julia> T = tropical_numbers(min);

julia> Txy,(x,y) = T["x","y"];

julia> f = x+y+1;

julia> tropicalLine = TropicalHypersurface(f);

julia> weights(tropicalLine)
# todo: add examples for varieties, curves and linear spaces
```
"""
function weights(TV::TropicalVarietySupertype{M,EMB}) where {M,EMB}
    # Question: should this return a vector or an iterator?
end # TODO!!!

@doc Markdown.doc"""
    PolyhedralComplex(TV::TropicalVarietySupertype)

Return the underlying polyhedral complex.

# Examples
```jldoctest
julia> T = tropical_numbers(min)
Tropical ring (min)

julia> Txy,(x,y) = T["x","y"]
(Multivariate Polynomial Ring in x, y over Tropical ring (min), AbstractAlgebra.Generic.MPoly{Oscar.TropicalNumbersElem{typeof(min)}}[x, y])

julia> f = x+y+1
x + y + (1)

julia> hyp = TropicalHypersurface(f)
A min tropical hypersurface embedded in 2-dimensional Euclidian space

julia> pc = PolyhedralComplex(hyp)
A polyhedral complex in ambient dimension 3

julia> vertices(pc)
4-element SubObjectIterator{Union{PointVector{Polymake.Rational}, RayVector{Polymake.Rational}}}:
 [0, -1, -1]
 [0, 1, 0]
 [0, 0, 1]
 [0, 1, 1]

julia> for v in vertices(pc)
       println(typeof(v))
       end
RayVector{Polymake.Rational}
RayVector{Polymake.Rational}
RayVector{Polymake.Rational}
PointVector{Polymake.Rational}
```
"""
function PolyhedralComplex(TV::TropicalVarietySupertype{M, EMB}) where {M,EMB}
    return PolyhedralComplex(pm_object(TV))
end
