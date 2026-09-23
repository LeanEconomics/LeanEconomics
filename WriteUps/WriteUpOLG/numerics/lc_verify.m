% Direct verification: saving of a zero-wealth household in the top income state, as a
% function of the interest rate, in the first period of a J-period life. Two solution
% methods: EGM, and value-function iteration with a fine grid search (no interpolation of
% the policy), which shares no code path with EGM.
function lc_verify
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); p=abs(V(:,k)); p=p/sum(p); y=exp(xg)'; y=y/(p'*y);
rr=[0.020 0.030 0.040 0.050 0.060];
for gamma=[1 3 5]
  fprintf('\n=== gamma=%g : saving g(a=0, z=7) in the first period of a %d-period life\n',gamma,J);
  fprintf('    r    |   EGM      |  VFI grid  | (VFI uses no interpolation)\n');
  for r=rr
    R=1+r; ag=[0; exp(linspace(log(1e-4),log(600),3999))'];
    c=egm_life(R,beta,gamma,y,Pi,ag,J); g_egm=y(nz)-c{J}(1,nz);
    g_vfi=vfi_first(R,beta,gamma,y,Pi,J);
    fprintf('  %.3f  | %10.6f | %10.6f\n',r,g_egm,g_vfi);
  end
end
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
function g0=vfi_first(R,beta,gamma,y,Pi,J)
nz=numel(y); na=3000; ag=linspace(0,60,na)'; m=y'+R*ag; V=u(m,gamma);
for k=1:J-2
  Vn=zeros(na,nz); EV=V*Pi';
  for z=1:nz
    for i=1:na
      cc=m(i,z)-ag; ok=cc>1e-12; vals=-inf(na,1); vals(ok)=u(cc(ok),gamma)+beta*EV(ok,z);
      Vn(i,z)=max(vals);
    end
  end
  V=Vn;
end
EV=V*Pi'; cc=y(nz)-ag; ok=cc>1e-12; vals=-inf(na,1);
vals(ok)=u(cc(ok),gamma)+beta*EV(ok,nz); [~,j]=max(vals); g0=ag(j);
end
function v=u(c,gam), if gam==1, v=log(c); else v=(c.^(1-gam)-1)/(1-gam); end, end
function c=egm_life(R,beta,gamma,y,Pi,ag,J)
nz=numel(y); na=numel(ag); m=y'+R*ag; c=cell(J,1); c{1}=m;
for k=1:J-1
  up=c{k}.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z);
  end
  cn=min(cn,m); c{k+1}=cn;
end
end
