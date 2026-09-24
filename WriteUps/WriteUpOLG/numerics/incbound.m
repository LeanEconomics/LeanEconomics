% A LOWER BOUND ON THE SUPPLY INCREMENT, allowing Theorem 1 to FAIL by a bounded amount.
%
% Couple the two economies on a common earnings path; d_j = a_j(r2) - a_j(r1), d_0 = 0.
%   d_{j+1} = [g_j^2(a_j^2) - g_j^2(a_j^1)] + [g_j^2(a_j^1) - g_j^1(a_j^1)]
% Second bracket >= -eps, with eps the worst failure of Theorem 1 in SAVING units.
% First bracket >= 0 when d_j >= 0 (g monotone in a), and >= L_j d_j when d_j < 0, with L_j the
% Lipschitz constant of saving in assets: dg/da = R(1 - MPC) <= R(1 - kap_k).  So
%   d_{j+1} >= L_j min(d_j, 0) - eps,   e_0 = 0, e_{j+1} = L_j e_j + eps,   d_j >= -e_j
% and  S(r2) - S(r1) >= -(1/J) sum_j e_j = -eps * Gamma.
% Single crossing needs  eps * Gamma  <  D(r1) - D(r2).
function incbound
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; alpha=9/25; delta=2/25;
[Pi,y,nu]=tauchen(rho,sigma,nz);
D=@(r) alpha/((1-alpha)*(r+delta));
na=500; ag=[0; exp(linspace(log(1e-3),log(4000),na-1))'];
for pr=[0.04 0.06; 0.02 0.08]'
  r1=pr(1); r2=pr(2); R1=1+r1; R2=1+r2; budget=D(r1)-D(r2);
  fprintf('\n############ r1=%.2f r2=%.2f :  budget D(r1)-D(r2) = %.4f ############\n',r1,r2,budget);
  fprintf(' gam |  eps    viol.mass | uniform bound | age-dep bound | MASS-WEIGHTED |  true dS\n');
  for gam=[1 2 3 5 8]
    [S1,M1,G1]=run(R1,beta,gam,y,Pi,nu,J,ag);
    [S2,M2,G2]=run(R2,beta,gam,y,Pi,nu,J,ag);
    % eps : worst failure of Theorem 1, over states REACHED by either economy
    epj=zeros(J,1);
    for j=1:J, for z=1:nz
      ok=(M1(:,z,j)>1e-12)|(M2(:,z,j)>1e-12);
      if any(ok), epj(j)=max(epj(j),max(G1(ok,z,j)-G2(ok,z,j))); end
    end, end
    epj=max(0,epj); eps=max(epj);
    % MASS-WEIGHTED violation at each age, under the r1 economy's own distribution:
    %   E[(d_{j+1})^-] <= L_j E[(d_j)^-] + Ebar_j,  Ebar_j = E_P[ (g^P - g^Q)^+ ]
    Eb=zeros(J,1); vmass=0;
    for j=1:J, for z=1:nz
      v=max(0,G1(:,z,j)-G2(:,z,j));
      Eb(j)=Eb(j)+sum(M1(:,z,j).*v);
      vmass=vmass+sum(M1(v>1e-10,z,j));
    end, end
    vmass=vmass/J;
    % Lipschitz constants from the sandwich MPC:  L_j = (1 - kap_{J-1-j}) R2
    Th=(beta*R2)^(1/gam); kap=zeros(J,1); kap(1)=1;
    for k=1:J-1, kap(k+1)=kap(k)*R2/(Th+kap(k)*R2); end
    L=zeros(J,1); for j=1:J, L(j)=(1-kap(J-j+1))*R2; end
    Gam=accum(L,J);
    Bu=eps*Gam;                    % uniform eps
    Ba=accumEps(L,epj,J);          % age-dependent eps_j
    Bw=accumEps(L,Eb,J);           % mass-weighted
    fprintf(' %3g | %.6f %.4f | %9.4f %s | %9.4f %s | %9.4f %s | %+.4f\n',...
       gam,eps,vmass,Bu,tick(Bu<budget),Ba,tick(Ba<budget),Bw,tick(Bw<budget),S2-S1);
  end
end
end
function B=accumEps(L,ep,J)
e=0; tot=0;
for j=1:J, tot=tot+e; if j<J, e=L(j)*e+ep(j); end, end
B=tot/J;
end
function G=accum(L,J)
e=0; tot=0;
for j=1:J, tot=tot+e; if j<J, e=L(j)*e+1; end, end
G=tot/J;
end
function s=tick(b), if b, s='PASS'; else, s='fail'; end, end
function [S,MU,GP]=run(R,beta,gam,y,Pi,nu,J,ag)
nz=numel(y); na=numel(ag); c=egm(R,beta,gam,y,Pi,ag,J); m=y'+R*ag;
MU=zeros(na,nz,J); GP=zeros(na,nz,J); mu=zeros(na,nz); mu(1,:)=nu'; tot=0;
for j=0:J-1
  k=J-1-j; ap=max(m-c{k+1},0); MU(:,:,j+1)=mu; GP(:,:,j+1)=ap; tot=tot+sum(mu,2)'*ag;
  if j==J-1, break; end
  new=zeros(na,nz);
  for z=1:nz
    w=mu(:,z); x=min(max(ap(:,z),ag(1)),ag(end));
    bin=discretize(x,ag); bin(isnan(bin))=na-1; bin=max(min(bin,na-1),1);
    frac=(x-ag(bin))./(ag(bin+1)-ag(bin));
    new=new+accumarray([bin;bin+1],[w.*(1-frac);w.*frac],[na 1])*Pi(z,:);
  end
  mu=new;
end
S=tot/J;
end
function c=egm(R,beta,gamma,y,Pi,ag,J)
nz=numel(y); na=numel(ag); m=y'+R*ag; c=cell(J,1); c{1}=m;
for k=1:J-1
  up=c{k}.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z);
  end
  c{k+1}=min(cn,m);
end
end
function [Pi,y,nu]=tauchen(rho,sigma,nz)
sd=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd; hi=(xg(j)+h/2-rho*xg(i))/sd;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,Dg]=eig(Pi'); [~,k]=max(abs(diag(Dg))); nu=abs(V(:,k)); nu=nu/sum(nu);
y=exp(xg)'; y=y/(nu'*y);
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
