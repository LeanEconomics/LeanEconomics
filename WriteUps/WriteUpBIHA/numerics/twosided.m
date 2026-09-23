% Two-sided certified time iteration for the log Aiyagari household (Rouwenhorst chain).
% Lower bounds: c >= t whenever t <= Th^-1 HM(L(m-t,.)); interpolation valid by concavity of c.
% Upper bounds: c <= t whenever t >= Th^-1 HM(U(m-t,.)); between grid points use
%   c(a') <= min(U(a_{k+1}), U(a_k) + min(R,(U(a_k)-L(a_{k-1}))/da)(a'-a_k)).
function twosided
beta=0.96; rho=0.9; sigma=0.4; nz=7;
% Rouwenhorst
p=(1+rho)/2; Pi=[p 1-p; 1-p p];
for k=3:nz, Z=zeros(k); Z(1:k-1,1:k-1)=Z(1:k-1,1:k-1)+p*Pi; Z(1:k-1,2:k)=Z(1:k-1,2:k)+(1-p)*Pi;
  Z(2:k,1:k-1)=Z(2:k,1:k-1)+(1-p)*Pi; Z(2:k,2:k)=Z(2:k,2:k)+p*Pi; Z(2:k-1,:)=Z(2:k-1,:)/2; Pi=Z; end
psi=sigma*sqrt(nz-1); xg=linspace(-psi,psi,nz);
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); pst=abs(V(:,k)); pst=pst/sum(pst);
y=exp(xg)'; y=y/(pst'*y); ymin=min(y); ymax=max(y);
fprintf('Rouwenhorst y = %s\n',mat2str(y',3)); fprintf('pi(4,:) = %s\n',mat2str(Pi(4,:),2));
lam=1/beta-1;
for r=[0.040, lam-3e-5]
  R=1+r; Th=beta*R; kappa=1-beta; s=kappa*R; onebR=1-beta*R;
  fprintf('\n==== r=%.6f  1-betaR=%.2e  kappa=%.3f\n',r,onebR,kappa);
  % truth on a fine grid
  amax=6000; na=3000; agf=[0; exp(linspace(log(1e-3),log(amax),na-1))'];
  c=solve_egm(R,beta,y,Pi,agf); ct=@(a,z) interp1(agf,c(:,z),a,'linear','extrap');
  % primitive bounds
  H=(R*eye(nz)-Pi)\(Pi*y);
  f=ymin*ones(nz,1);
  for it=1:2000, Mh=1./(Pi*(1./f)); fn=min(y,(Mh+s*y)/(Th+s)); if max(abs(fn-f))<1e-13,break;end; f=fn; end
  % coarse grid
  da=0.05; ag=(0:da:16)'; K=numel(ag);
  L=repmat(f',K,1)+s*ag; U=min(R*ag+y', kappa*(R*ag+y'+H'));
  Lfun=@(a,z,L) lowerinterp(a,z,L,ag,f,s); Ufun=@(a,z,U,L) upperinterp(a,z,U,L,ag,da,R,kappa,y,H);
  report(0,L,U,ct,ag,y,Pi,onebR,ymin);
  for n=1:300
    Ln=L; Un=U;
    for z=1:nz, m=R*ag+y(z); pz=Pi(z,:);
      for k=1:K
        % lower: largest t in [0,m] with t <= Th^-1 HM(L(m-t,.))
        g=@(t) t - (1/Th)./(pz*(1./Lfun(m(k)-t,1:nz,L)'));
        if g(m(k))<=0, Ln(k,z)=m(k); else, Ln(k,z)=bisect(g,0,m(k),1e-10); end
        % upper: smallest t in [0,m] with t >= Th^-1 HM(U(m-t,.))
        h=@(t) t - (1/Th)./(pz*(1./Ufun(m(k)-t,1:nz,U,L)'));
        if h(m(k))<0, Un(k,z)=m(k); else, Un(k,z)=bisect(h,0,m(k),1e-10); end
      end
    end
    L=max(L,Ln); U=min(U,Un);   % monotone iteration
    if ismember(n,[1 2 5 10 20 50 100 200 300]), report(n,L,U,ct,ag,y,Pi,onebR,ymin); end
  end
end
end
function t=bisect(g,lo,hi,tol)
  for i=1:60, mid=(lo+hi)/2; if g(mid)<=0, lo=mid; else, hi=mid; end; if hi-lo<tol, break; end; end; t=lo;
end
function v=lowerinterp(a,zs,L,ag,f,s)
  % linear interpolation (valid by concavity of c); beyond grid: affine primitive floor
  v=zeros(1,numel(zs));
  for j=1:numel(zs), z=zs(j);
    if a<=ag(end), v(j)=interp1(ag,L(:,z),max(a,0)); else, v(j)=f(z)+s*a; end
  end
end
function v=upperinterp(a,zs,U,L,ag,da,R,kappa,y,H)
  v=zeros(1,numel(zs)); a=max(a,0);
  for j=1:numel(zs), z=zs(j);
    if a>=ag(end), v(j)=kappa*(R*a+y(z)+H(z)); continue; end
    k=floor(a/da)+1; if abs(a-ag(k))<1e-12, v(j)=U(k,z); continue; end
    slope=R; if k>1, slope=min(R,(U(k,z)-L(k-1,z))/da); end
    v(j)=min(U(k+1,z), U(k,z)+slope*(a-ag(k)));
  end
end
function report(n,L,U,ct,ag,y,Pi,onebR,ymin)
  nz=numel(y); sel=ag<=6; Kt=sum(sel); C=zeros(Kt,nz); for z=1:nz, C(:,z)=ct(ag(sel),z); end
  eL=max(C-L(sel,:)); eU=max(U(sel,:)-C);
  % certification of pairs (z-1,z+1) on a'<=5
  A0=5; sel5=ag<=A0; v0=inf; worst='';
  for z=1:nz
    z1=max(z-1,1); z2=min(z+1,nz); if z1==z2, z2=z1+1; end
    p0=min(Pi(z,z1),Pi(z,z2)); gap=1./U(sel5,z1)-1./L(sel5,z2);
    if any(gap<=0), v0=0; worst=sprintf('%s z=%d(%d,%d) fails at a=%.2f;',worst,z,z1,z2,ag(find(gap<=0,1))); else
      v=p0/2*min(gap)^2; if v<v0, v0=v; worst=sprintf('z=%d(%d,%d) p0=%.3f mingap=%.3f',z,z1,z2,p0,min(gap)); end
    end
  end
  thr=v0/(2/ymin^2)*(1-4.62/A0);
  fprintf('n=%3d: max(c-L) on [0,6] by z = %s\n       max(U-c) on [0,6] by z = %s\n       v0=%.2e (%s) -> need 1-betaR < %.2e (have %.2e)\n',n,mat2str(eL,2),mat2str(eU,2),v0,worst,thr,onebR);
end
function c=solve_egm(R,beta,y,Pi,ag)
nz=numel(y); na=numel(ag); kappa=1-beta; m=y'+R*ag; c=kappa*m+kappa*max(y)/(R-1); c=min(c,m);
for it=1:200000
  rhs=beta*R*((1./c)*Pi'); cend=1./rhs; mend=cend+ag; cnew=zeros(na,nz);
  for z=1:nz, cnew(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap'); corner=m(:,z)<mend(1,z); cnew(corner,z)=m(corner,z); end
  cnew=min(cnew,m); err=max(abs(1./cnew(:)-1./c(:)).*c(:)); c=cnew; if err<1e-11, break; end
end
end
