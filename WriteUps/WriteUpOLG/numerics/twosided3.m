% The margin chain needs >= 75-90% of the TRUE stage difference (twosided2.m).  The one natural
% primitive candidate for a margin is the certainty-equivalent household's extra saving,
%   s_k(a,z) = max( g^CE_k(a,z;R2) - g^CE_k(a,z;R1), 0 ),  g^CE_k = m - kap_k (m + H_k(z)),
% H_k(z) = E[sum_{i<=k} y_{t+i} R^{-i} | z].  Slope on [b1,b1+s]: exact chord (best case).
function twosided3
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
[Pi,y]=tauchen(rho,sigma,nz);
na=400; ag=[0; exp(linspace(log(1e-3),log(300),na-1))'];
r1=0.04; dr=0.02; R1=1+r1; R2=1+r1+dr;
for gam=[2 3]
  c1=egm(R1,beta,gam,y,Pi,ag,J); c2=egm(R2,beta,gam,y,Pi,ag,J);
  m1=y'+R1*ag; m2=y'+R2*ag;
  [kap1,H1]=ce(R1,beta,gam,y,Pi,J); [kap2,H2]=ce(R2,beta,gam,y,Pi,J);
  gce=@(k,a,z,R,kap,H) (y(z)+R*a) - kap(k+1)*(y(z)+R*a+H(k+1,z));   % stage k, k>=0
  reach=zeros(J,1); a=0;
  for j=1:J-1, k=J-j; a=max(y(end)+R2*a-interp1(ag,c2{k+1}(:,end),a,'linear','extrap'),0); reach(j+1)=a; end
  for scale=[1 0.5 0.25]
    nf=0; nt=0; worst=inf; wk=0; wa=0; wz=0; nf0=0; nt0=0; ratio=[];
    for k=1:J-2
      Ck1=c1{k+1}; Ck2=c2{k+1}; Cn1=c1{k+2}; Cn2=c2{k+2}; rj=reach(J-k);
      for z=1:nz
        for i=1:na
          a=ag(i); if a>rj, break; end
          cc1=Cn1(i,z); b1=m1(i,z)-cc1; if b1<=1e-9, continue; end
          b2=m2(i,z)-Cn2(i,z);
          s=scale*max(gce(k+1,a,z,R2,kap2,H2)-gce(k+1,a,z,R1,kap1,H1),0);
          if b2-b1>1e-6, ratio(end+1)=s/(b2-b1); end
          lhs=0; rhs=0;
          for zp=1:nz
            C1p=interp1(ag,Ck1(:,zp),b1,'linear','extrap'); bb=b1+s;
            C1pp=interp1(ag,Ck1(:,zp),bb,'linear','extrap'); rise=C1pp-C1p;
            g1=y(zp)+R1*bb-C1pp;
            skp=0; if g1>1e-9, skp=scale*max(gce(k,bb,zp,R2,kap2,H2)-gce(k,bb,zp,R1,kap1,H1),0); end
            arg=C1p+rise+dr*b1-skp;
            lhs=lhs+Pi(z,zp)*arg^(-gam); rhs=rhs+Pi(z,zp)*C1p^(-gam);
          end
          lhs=R2*lhs; rhs=R1*(1+(dr*a-s)/cc1)^(-gam)*rhs;
          mg=lhs/rhs-1; f=mg<0; nt=nt+1; nf=nf+f; if i==1, nt0=nt0+1; nf0=nf0+f; end
          if mg<worst, worst=mg; wk=k+1; wa=a; wz=z; end
        end
      end
    end
    fprintf('gamma=%d  CE margin x%.2f : fail %6.2f%%  worst %+8.4f at (k=%2d,a=%6.2f,z=%d)  fail at a=0 %6.2f%%  CE/true margin ratio: median %.2f, 10%%-90%% [%.2f, %.2f]\n',...
      gam,scale,100*nf/nt,worst,wk,wa,wz,100*nf0/nt0,median(ratio),quantile(ratio,0.1),quantile(ratio,0.9));
  end
end
end
function [kap,H]=ce(R,beta,gam,y,Pi,J)
Th=(beta*R)^(1/gam); nz=numel(y);
kap=zeros(J,1); kap(1)=1; for k=1:J-1, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
H=zeros(J,nz); for k=1:J-1, H(k+1,:)=(Pi*(y+H(k,:)'))'/R; end
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
function [Pi,y]=tauchen(rho,sigma,nz)
sd=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd; hi=(xg(j)+h/2-rho*xg(i))/sd;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,Dg]=eig(Pi'); [~,k]=max(abs(diag(Dg))); nu=abs(V(:,k)); nu=nu/sum(nu);
y=exp(xg)'; y=y/(nu'*y);
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
