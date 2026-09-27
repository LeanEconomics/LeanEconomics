% twosided.m showed the margin route loses because C2(b2) <= C2(b1+s) <= C1(b1+s)+... was bounded with
% the consumption SLOPE R (a unit MPC).  Here the slope over [b1, b1+s] is replaced by
%   'exact' : the true chord of C1 on [b1,b1+s]           (least lossy possible version of the chain)
%   'chord0': concavity, slope <= (C1(b1)-C1(0))/b1        (a primitive-shaped bound, true values)
%   'R'     : the unit slope of twosided.m
% If 'exact' fails at every phi the two-sided margin chain is dead as a mechanism.
function twosided2
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
[Pi,y]=tauchen(rho,sigma,nz);
na=400; ag=[0; exp(linspace(log(1e-3),log(300),na-1))'];
r1=0.04; dr=0.02; R1=1+r1; R2=1+r1+dr;
for gam=[2 3]
  c1=egm(R1,beta,gam,y,Pi,ag,J); c2=egm(R2,beta,gam,y,Pi,ag,J);
  m1=y'+R1*ag; m2=y'+R2*ag;
  reach=zeros(J,1); a=0;
  for j=1:J-1, k=J-j; a=max(y(end)+R2*a-interp1(ag,c2{k+1}(:,end),a,'linear','extrap'),0); reach(j+1)=a; end
  for mode=["exact" "chord0" "R"]
    fprintf('gamma=%d slope=%-6s: phi | fail%% | worst LHS/RHS-1 at (k,a,z) | fail%% young(k>=40) | fail%% old(k<=20) | fail%% a=0\n',gam,mode);
    for phi=[0 0.25 0.5 0.75 1.0]
      nf=0; nt=0; worst=inf; wk=0; wa=0; wz=0; nfy=0; nty=0; nfo=0; nto=0; nf0=0; nt0=0;
      for k=1:J-2
        Ck1=c1{k+1}; Ck2=c2{k+1}; Cn1=c1{k+2}; Cn2=c2{k+2}; rj=reach(J-k);
        for z=1:nz
          for i=1:na
            a=ag(i); if a>rj, break; end
            cc1=Cn1(i,z); b1=m1(i,z)-cc1; if b1<=1e-9, continue; end
            b2=m2(i,z)-Cn2(i,z); s=phi*max(b2-b1,0);
            lhs=0; rhs=0;
            for zp=1:nz
              C1p=interp1(ag,Ck1(:,zp),b1,'linear','extrap'); bb=b1+s;
              C1pp=interp1(ag,Ck1(:,zp),bb,'linear','extrap');
              switch mode
                case "exact",  rise=C1pp-C1p;
                case "chord0", rise=s*(C1p-Ck1(1,zp))/b1;
                case "R",      rise=R2*s;
              end
              g1=y(zp)+R1*bb-C1pp; g2=y(zp)+R2*bb-interp1(ag,Ck2(:,zp),bb,'linear','extrap');
              skp=0; if g1>1e-9, skp=phi*max(g2-g1,0); end
              arg=C1p+rise+dr*b1-skp;
              lhs=lhs+Pi(z,zp)*arg^(-gam); rhs=rhs+Pi(z,zp)*C1p^(-gam);
            end
            lhs=R2*lhs; rhs=R1*(1+(dr*a-s)/cc1)^(-gam)*rhs;
            mg=lhs/rhs-1; f=mg<0; nt=nt+1; nf=nf+f;
            if k+1>=40, nty=nty+1; nfy=nfy+f; end
            if k+1<=20, nto=nto+1; nfo=nfo+f; end
            if i==1, nt0=nt0+1; nf0=nf0+f; end
            if mg<worst, worst=mg; wk=k+1; wa=a; wz=z; end
          end
        end
      end
      fprintf('   %.2f | %6.2f%% | %+8.4f (%2d,%6.2f,%d) | %6.2f%% | %6.2f%% | %6.2f%%\n',phi,100*nf/nt,worst,wk,wa,wz,100*nfy/max(nty,1),100*nfo/max(nto,1),100*nf0/max(nt0,1));
    end
  end
end
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
