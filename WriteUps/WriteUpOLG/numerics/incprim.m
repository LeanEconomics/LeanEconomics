% LEAD 1: bound the failure of Theorem 1 from PRIMITIVES and run it through the increment envelope.
%   V_j(z) <= sup_a [ c2^ceil(a,z) - c1^floor(a,z) - dr a ]^+
% with c2^ceil = kap2 (m2 + Hup2(z))   (arithmetic human-wealth CEILING at R2)  and
%      c1^floor = kap1 (m1 + G1(a,z))   (asset-incidence FLOOR at R1, the sharpest floor).
% (G is a floor: assetHumanWealth_le_stageConsumption.  First version of this file used it as a ceiling.)
% ebar_j <= sum_z nu_z V_j(z); accumulate e_{j+1} = L_j e_j + ebar_j, L_j = (1-kap)R2;
% single crossing needs mean_j e_j < D(r1) - D(r2) = 0.670 over [4%,6%].
% Also: which side is lossy (true c2 with floor c1; ceiling c2 with true c1).
function incprim
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; alpha=9/25; delta=2/25;
[Pi,y,nu]=tauchen(rho,sigma,nz);
D=@(r) alpha/((1-alpha)*(r+delta));
r1=0.04; r2=0.06; R1=1+r1; R2=1+r2; dr=r2-r1; budget=D(r1)-D(r2);
na=300; ag=[0; exp(linspace(log(1e-3),log(300),na-1))'];
fprintf('budget D(r1)-D(r2) = %.4f\n',budget);
fprintf(' gam | mean_j ebar: primitive | c2 true+c1 floor | c2 ceil+c1 true | true nu-exact || accumulated: prim | c2true | c1true | true || worst state (j,z,a) prim\n');
for gam=[1 1.5 2 3]
  [kap1,Hr1,G1,Hup1]=bounds(R1,beta,gam,y,Pi,J,ag);
  [kap2,Hr2,G2,Hup2]=bounds(R2,beta,gam,y,Pi,J,ag);
  c1=egm(R1,beta,gam,y,Pi,ag,J); c2=egm(R2,beta,gam,y,Pi,ag,J);
  m1=y'+R1*ag; m2=y'+R2*ag;
  reach=zeros(J,1); a=0;
  for j=1:J-1, k=J-j; a=max(y(end)+R2*a-interp1(ag,c2{k+1}(:,end),a,'linear','extrap'),0); reach(j+1)=a; end
  eb=zeros(J,6); worst=0; ws=[0 0 0];
  CP2=ceilpm(R2,beta,gam,y,Pi,J,ag,kap2,G2);
  for j=1:J           % age j has k = J-j periods to go; stage index k+1
    k=J-j; rj=reach(j); ia=find(ag<=rj);
    ceil2=kap2(k+1)*(m2(ia,:)+repmat(Hup2(:,k+1)',numel(ia),1)); flo1=kap1(k+1)*(m1(ia,:)+G1(ia,:,k+1));
    ceilP=CP2(ia,:,k+1);
    t1=c1{k+1}(ia,:); t2=c2{k+1}(ia,:); dra=repmat(dr*ag(ia),1,nz);
    v=[max(ceil2-flo1-dra,0); max(t2-flo1-dra,0); max(ceil2-t1-dra,0); max(t2-t1-dra,0); max(ceilP-flo1-dra,0); max(ceilP-t1-dra,0)];
    v=reshape(v,numel(ia),6,nz);
    for s=1:6, for z=1:nz, eb(j,s)=eb(j,s)+nu(z)*max(v(:,s,z)); end, end
    [mx,iz]=max(max(v(:,5,:),[],1)); if mx>worst, worst=mx; [~,im]=max(v(:,5,iz)); ws=[j iz ag(ia(im))]; end
    if j==1 || j==30, fprintf('    age %2d: ceilP/true worst ratio %.3f (max over grid %.3f), floor/true worst %.3f\n',j,min(t2(:)./ceilP(:)),max(ceilP(:)./t2(:)),min(flo1(:)./t1(:))); end
  end
  Th=(beta*R2)^(1/gam); L=zeros(J,1); for j=1:J, L(j)=(1-kap2(J-j+1))*R2; end
  B=zeros(1,6); for s=1:6, B(s)=accumEps(L,eb(:,s),J); end
  fprintf(' %3.1f | mean ebar: arith-ceil %.4f | truec2+floor %.4f | arith-ceil+truec1 %.4f | true %.4f | PM-CEIL+floor %.4f | PM-ceil+truec1 %.4f || accumulated: %.3f %.3f %.3f %.4f  PM: %.3f %.3f || worst PM state (j,z,a) (%2d,%d,%.2f) %.3f\n',...
    gam,mean(eb(:,1)),mean(eb(:,2)),mean(eb(:,3)),mean(eb(:,4)),mean(eb(:,5)),mean(eb(:,6)),B,ws,worst);
end
end
function [kap,H,G,Hup]=bounds(R,beta,gam,y,Pi,J,ag)
nz=numel(y); na=numel(ag); Th=(beta*R)^(1/gam); K=J-1;
kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
Hup=zeros(nz,J); for k=1:K, Hup(:,k+1)=(Pi*(y+Hup(:,k)))/R; end
H=zeros(nz,J);
for k=1:K
  M=zeros(nz,1);
  for z=1:nz, M(z)=(sum(Pi(z,:)'.*(y+H(:,k)).^(-gam)))^(-1/gam); end
  H(:,k+1)=min(M/R,(1/kap(k+1)-1)*y);
end
G=zeros(na,nz,J);
for k=1:K
  phi=zeros(na,nz); Gn=zeros(na,nz);
  for z=1:nz, phi(:,z)=max(0,(1-kap(k+1))*(y(z)+R*ag)-kap(k+1)*Hup(z,k+1)); end
  for z=1:nz
    Gk=zeros(na,nz);
    for w=1:nz, Gk(:,w)=interp1(ag,G(:,w,k),min(max(phi(:,z),ag(1)),ag(end)),'linear','extrap'); end
    Mz=(sum(Pi(z,:).*((y'+Gk).^(-gam)),2)).^(-1/gam);
    Gn(:,z)=min(Mz/R,(1/kap(k+1)-1)*(y(z)+R*ag));
  end
  G(:,:,k+1)=Gn;
end
end
function CP=ceilpm(R,beta,gam,y,Pi,J,ag,kap,G)
% power-mean ceiling: CP_0 = m; CP_{k+1}(a,z) = min(m, [bR sum_z' pi CP_k(abar',z')^-g]^(-1/g)),
% abar' = max(m - kap_{k+1}(m + G_{k+1}(a,z)), 0)  (saving ceiling from the consumption floor).
nz=numel(y); na=numel(ag); m=y'+R*ag; CP=zeros(na,nz,J); CP(:,:,1)=m;
for k=1:J-1
  for z=1:nz
    abar=max(m(:,z)-kap(k+1)*(m(:,z)+G(:,z,k+1)),0);
    acc=zeros(na,1);
    for zp=1:nz, acc=acc+Pi(z,zp)*interp1(ag,CP(:,zp,k),min(abar,ag(end)),'linear','extrap').^(-gam); end
    CP(:,z,k+1)=min(m(:,z),(beta*R*acc).^(-1/gam));
  end
end
end
function B=accumEps(L,ep,J)
e=0; tot=0;
for j=1:J, tot=tot+e; if j<J, e=L(j)*e+ep(j); end, end
B=tot/J;
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
