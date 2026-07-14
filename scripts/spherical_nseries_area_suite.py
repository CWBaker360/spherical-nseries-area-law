#!/usr/bin/env python3
"""Reproducibility suite for the spherical N-Series area-law paper.

The default ``smoke`` case is deliberately inexpensive.  The named cases
implement the same geometry used in the paper and can be run at larger scales
by increasing ``--N`` and ``--dps``.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Callable, Iterable

import mpmath as mp

Vec = tuple[mp.mpf, mp.mpf, mp.mpf]


def dot(a: Vec, b: Vec) -> mp.mpf:
    return a[0]*b[0] + a[1]*b[1] + a[2]*b[2]


def cross(a: Vec, b: Vec) -> Vec:
    return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])


def add(a: Vec, b: Vec) -> Vec:
    return (a[0]+b[0], a[1]+b[1], a[2]+b[2])


def sub(a: Vec, b: Vec) -> Vec:
    return (a[0]-b[0], a[1]-b[1], a[2]-b[2])


def scale(a: Vec, s: mp.mpf) -> Vec:
    return (s*a[0], s*a[1], s*a[2])


def norm(a: Vec) -> mp.mpf:
    return mp.sqrt(dot(a,a))


def normalize(a: Vec) -> Vec:
    n=norm(a)
    if n == 0:
        raise ZeroDivisionError('zero vector')
    return (a[0]/n,a[1]/n,a[2]/n)


def chord_area(a: Vec,b: Vec,c: Vec) -> mp.mpf:
    return mp.mpf('0.5')*norm(cross(sub(b,a),sub(c,a)))


def deg(x) -> mp.mpf:
    return mp.mpf(x)*mp.pi/180


def sph(lat: mp.mpf, lon: mp.mpf) -> Vec:
    cl=mp.cos(lat)
    return (cl*mp.cos(lon),cl*mp.sin(lon),mp.sin(lat))


def tangent_direction(p: Vec,q: Vec) -> Vec:
    return normalize(sub(q,scale(p,dot(p,q))))


def spherical_polygon_area(vertices: list[Vec]) -> mp.mpf:
    total=mp.mpf('0')
    n=len(vertices)
    for i,p in enumerate(vertices):
        a=tangent_direction(p,vertices[(i-1)%n])
        b=tangent_direction(p,vertices[(i+1)%n])
        d=max(mp.mpf('-1'),min(mp.mpf('1'),dot(a,b)))
        total += mp.acos(d)
    return total-(n-2)*mp.pi


def n2(a,b): return b+(b-a)/3

def n3(a,b,c): return a/45-mp.mpf(4)*b/9+mp.mpf(64)*c/45

def n4(a,b,c,d): return -a/2835+mp.mpf(4)*b/135-mp.mpf(64)*c/135+mp.mpf(4096)*d/2835


def order(e1,e2):
    return mp.log(e1/e2)/mp.log(2)


def evaluate(approx: Callable[[int],mp.mpf], exact: mp.mpf, N: int) -> dict[str,mp.mpf]:
    vals=[approx(N*(2**j)) for j in range(5)]
    def acc(v):
        return [v[0],n2(v[0],v[1]),n3(v[0],v[1],v[2]),n4(v[0],v[1],v[2],v[3])]
    a0=acc(vals[:4]); a1=acc(vals[1:5])
    errs0=[abs(x-exact) for x in a0]; errs1=[abs(x-exact) for x in a1]
    return {
        'N':N,
        'raw_order':order(errs0[0],errs1[0]),
        'two_order':order(errs0[1],errs1[1]),
        'three_order':order(errs0[2],errs1[2]),
        'four_order':order(errs0[3],errs1[3]),
        'raw_error':errs0[0], 'two_error':errs0[1], 'three_error':errs0[2], 'four_error':errs0[3],
    }


def cap_exact(alpha): return 2*mp.pi*(1-mp.cos(alpha))

def cap_polygon(alpha,N):
    h=2*mp.pi/N; c=mp.cos(alpha); s=mp.sin(alpha)
    tri=2*mp.atan2(s*s*mp.sin(h),1+2*c+c*c+s*s*mp.cos(h))
    return N*tri


def bary_point(A,B,C,i,j,N):
    return normalize(add(add(scale(A,mp.mpf(N-i-j)/N),scale(B,mp.mpf(i)/N)),scale(C,mp.mpf(j)/N)))


def chordal_triangle(A,B,C,N):
    pts={(i,j):bary_point(A,B,C,i,j,N) for i in range(N+1) for j in range(N+1-i)}
    total=mp.mpf('0')
    for i in range(N):
        for j in range(N-i):
            total += chord_area(pts[i,j],pts[i+1,j],pts[i,j+1])
            if i+j <= N-2:
                total += chord_area(pts[i+1,j],pts[i+1,j+1],pts[i,j+1])
    return total


def right_triangle(beta,N):
    return chordal_triangle((mp.mpf(0),mp.mpf(0),mp.mpf(1)),(mp.mpf(1),mp.mpf(0),mp.mpf(0)),(mp.cos(beta),mp.sin(beta),mp.mpf(0)),N)


def latlon_area(lat0,lat1,lon0,lon1,N,perturb=mp.mpf('0'),seed=1):
    def smooth(u,v,channel):
        env=u*(1-u)*v*(1-v)
        a1=1+((seed+2*channel)%4); b1=1+((2*seed+channel+1)%5)
        a2=1+((3*seed+channel+2)%5); b2=1+((seed+3*channel+3)%4)
        ph1=mp.mpf(seed+channel)*mp.pi/7; ph2=mp.mpf(2*seed+channel+1)*mp.pi/11
        val=mp.sin(2*mp.pi*(a1*u+b1*v)+ph1)+mp.mpf('.5')*mp.cos(2*mp.pi*(a2*u-b2*v)+ph2)+mp.mpf('.25')*mp.sin(2*mp.pi*((a1+a2)*u)+ph2)
        return 4*env*val
    pts={}
    h=mp.mpf(1)/N
    for i in range(N+1):
        for j in range(N+1):
            u=mp.mpf(i)/N; v=mp.mpf(j)/N
            if 0<i<N and 0<j<N and perturb:
                u += perturb*h*smooth(u,v,0); v += perturb*h*smooth(u,v,1)
                margin=mp.mpf('.1')*h
                u=max(margin,min(1-margin,u)); v=max(margin,min(1-margin,v))
            pts[i,j]=sph(lat0+u*(lat1-lat0),lon0+v*(lon1-lon0))
    total=mp.mpf('0')
    for i in range(N):
        for j in range(N):
            p00,p10,p01,p11=pts[i,j],pts[i+1,j],pts[i,j+1],pts[i+1,j+1]
            total += chord_area(p00,p10,p11)+chord_area(p00,p11,p01)
    return total


def latlon_exact(lat0,lat1,lon0,lon1): return (lon1-lon0)*(mp.sin(lat1)-mp.sin(lat0))


def default_polygon():
    return [sph(deg(a),deg(b)) for a,b in [(4,-8),(18,5),(15,28),(2,42),(-14,30),(-10,4)]]


def chordal_polygon(vertices,N):
    return sum((chordal_triangle(vertices[0],vertices[i],vertices[i+1],N) for i in range(1,len(vertices)-1)),mp.mpf('0'))


def tangent_basis(center):
    east=cross((mp.mpf(0),mp.mpf(0),mp.mpf(1)),center)
    east=(mp.mpf(1),mp.mpf(0),mp.mpf(0)) if norm(east)<mp.mpf('1e-40') else normalize(east)
    return east,normalize(cross(center,east))


def exp_map(center,t):
    r=norm(t)
    return center if r==0 else add(scale(center,mp.cos(r)),scale(t,mp.sin(r)/r))


def generated_polygon(seed,nverts,radius_deg=22,jitter=mp.mpf('.35')):
    center=sph(deg(4),deg(12)); east,north=tangent_basis(center); base=deg(radius_deg)
    out=[]
    for j in range(nverts):
        theta=2*mp.pi*j/nverts+jitter*mp.mpf('.18')*mp.sin(mp.mpf(seed+j+1)*mp.mpf('1.217'))
        val=mp.sin(mp.mpf(seed+3*j+1)*mp.mpf('1.713'))+mp.mpf('.5')*mp.cos(mp.mpf(2*seed+5*j+nverts)*mp.mpf('.917'))
        r=base*(1+jitter*val/mp.mpf('1.8'))
        r=max(base*mp.mpf('.25'),r)
        out.append(exp_map(center,add(scale(east,r*mp.cos(theta)),scale(north,r*mp.sin(theta)))))
    return out


def moment_check() -> bool:
    sets=[([mp.mpf(-1)/3,mp.mpf(4)/3],[1,2],1),([mp.mpf(1)/45,-mp.mpf(4)/9,mp.mpf(64)/45],[1,2,4],2),([-mp.mpf(1)/2835,mp.mpf(4)/135,-mp.mpf(64)/135,mp.mpf(4096)/2835],[1,2,4,8],3)]
    for weights,scales,count in sets:
        if abs(sum(weights)-1)>mp.mpf('1e-60'): return False
        for j in range(1,count+1):
            if abs(sum(w/mp.mpf(s)**(2*j) for w,s in zip(weights,scales)))>mp.mpf('1e-60'): return False
    return True


def row_to_plain(name,row):
    return {'case':name, **{k:(int(v) if k=='N' else mp.nstr(v,18)) for k,v in row.items()}}


def run_case(case,N):
    if case=='cap':
        a=deg(30); return evaluate(lambda n:cap_polygon(a,n),cap_exact(a),N)
    if case=='triangle':
        b=deg(30); return evaluate(lambda n:right_triangle(b,n),b,N)
    if case=='latlon':
        x=(deg(-15),deg(15),deg(0),deg(30)); return evaluate(lambda n:latlon_area(*x,n),latlon_exact(*x),N)
    if case=='irregular':
        v=default_polygon(); exact=spherical_polygon_area(v)
        if exact<0: v=list(reversed(v)); exact=spherical_polygon_area(v)
        return evaluate(lambda n:chordal_polygon(v,n),exact,N)
    if case=='perturbed':
        x=(deg(-15),deg(15),deg(0),deg(30)); return evaluate(lambda n:latlon_area(*x,n,perturb=mp.mpf('.10'),seed=1),latlon_exact(*x),N)
    raise ValueError(case)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--case',choices=['smoke','cap','triangle','latlon','irregular','perturbed','all'],default='smoke')
    ap.add_argument('--N',type=int,default=4)
    ap.add_argument('--dps',type=int,default=70)
    ap.add_argument('--outdir',type=Path,default=Path('output'))
    args=ap.parse_args(); mp.mp.dps=args.dps; args.outdir.mkdir(parents=True,exist_ok=True)
    cases=['cap','triangle','latlon','irregular','perturbed'] if args.case in ('smoke','all') else [args.case]
    rows=[]
    for case in cases:
        row=run_case(case,args.N)
        rows.append(row_to_plain(case,row))
    checks={
        'moment_conditions_passed':moment_check(),
        'all_results_finite':all(all(mp.isfinite(mp.mpf(v)) for k,v in r.items() if k not in ('case','N')) for r in rows),
        'regular_raw_orders_near_two':all(mp.mpf(r['raw_order'])>mp.mpf('1.75') for r in rows if r['case']!='perturbed'),
        'regular_two_scale_improves_order':all(mp.mpf(r['two_order'])>mp.mpf('3.3') for r in rows if r['case'] in ('cap','triangle','latlon','irregular')),
        'smoke_verification_passed':False,
    }
    checks['smoke_verification_passed']=all(v for k,v in checks.items() if k!='smoke_verification_passed')
    with (args.outdir/'smoke_results.csv').open('w',newline='',encoding='utf-8') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
    (args.outdir/'smoke_summary.json').write_text(json.dumps({'precision_dps':args.dps,'base_N':args.N,'checks':checks,'rows':rows},indent=2)+'\n',encoding='utf-8')
    text='\n'.join([f'{k}: {v}' for k,v in checks.items()])+'\n'
    (args.outdir/'smoke_summary.txt').write_text(text,encoding='utf-8')
    print(text,end='')
    if not checks['smoke_verification_passed']:
        raise SystemExit(1)

if __name__=='__main__': main()
