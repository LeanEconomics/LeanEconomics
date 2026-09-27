% Two-sided invariant for the stage induction: Theorem 1 WITH A MARGIN,
%     g_k(a,z;R2) - g_k(a,z;R1) >= s_k(a,z) >= 0,        s_k = 0 where the R1 household is at a corner.
% Step at stage k+1, state (a,z), b1 = g_{k+1}(a;R1) > 0.  If the margin fails, b2 < b1 + s, so
% c2 > c1 + dr a - s and u'(c2) <= u'(c1 + dr a - s).  Euler under the cap (R2) and above the floor (R1),
% monotone consumption, slope of c in a at most R, and the stage-k margin give
%   C2(b2) <= C2(b1+s) <= C1(b1+s) + dr (b1+s) - s_k(b1+s,z') <= C1(b1) + R2 s + dr b1 - s_k(b1+s,z'),
% so the step closes at (a,z) iff
%   R2 E[(C1(b1) + R2 s + dr b1 - s_k(b1+s,z'))^-g]  >=  R1 (1 + (dr a - s)/c1)^-g E[C1(b1)^-g].   (***)
% phi = 0 is StageSlack.  Margins are taken as phi x the TRUE stage difference (the most favourable
% self-consistent profile), to see whether ANY margin closes the step.
function twosided
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
[Pi,y]=tauchen(rho,sigma,nz);
na=400; ag=[0; exp(linspace(log(1e-3),log(300),na-1))'];
for gam=[2 3]
 for dr=[0.02 0.005]
  r1=0.04; R1=1+r1; R2=1+r1+dr;
  c1=egm(R1,beta,gam,y,Pi,ag,J); c2=egm(R2,beta,gam,y,Pi,ag,J);
  m1=y'+R1*ag; m2=y'+R2*ag;
  % reach along the max-income path at R2
  reach=zeros(J,1); a=0;
  for j=1:J-1, k=J-j; a=max(y(end)+R2*a-interp1(ag,c2{k+1}(:,end),a,'linear','extrap'),0); reach(j+1)=a; end
  fprintf('gamma=%d dr=%.3f : phi | fail%% (reachable, b1>0) | worst LHS/RHS-1 | worst at (k,a,z) | T1 fails%%\n',gam,dr);
  for phi=[0 0.25 0.5 0.75 0.9 1.0]
    nf=0; nt=0; worst=inf; wk=0; wa=0; wz=0; nT1=0;
    for k=1:J-2                      % c{k+1} = stage k, c{k+2} = stage k+1
      Ck1=c1{k+1}; Ck2=c2{k+1};      % stage k (next period) at the two rates, index k+1
      Cn1=c1{k+2}; Cn2=c2{k+2};      % stage k+1 (today)
      rj=reach(J-k);                 % cohort with k+1 periods to go is age J-k-1 -> index J-k
      for z=1:nz
        for i=1:na
          a=ag(i); if a>rj, break; end
          cc1=Cn1(i,z); b1=m1(i,z)-cc1; if b1<=1e-9, continue; end
          b2=m2(i,z)-Cn2(i,z);
          diff=b2-b1; if diff<0, nT1=nT1+1; end
          s=phi*max(diff,0); nt=nt+1;
          lhs=0; rhs=0;
          for zp=1:nz
            C1p=interp1(ag,Ck1(:,zp),b1,'linear','extrap');
            bb=b1+s;
            g1=y(zp)+R1*bb-interp1(ag,Ck1(:,zp),bb,'linear','extrap');
            g2=y(zp)+R2*bb-interp1(ag,Ck2(:,zp),bb,'linear','extrap');
            skp=0; if g1>1e-9, skp=phi*max(g2-g1,0); end
            arg=C1p+R2*s+dr*b1-skp;
            lhs=lhs+Pi(z,zp)*arg^(-gam); rhs=rhs+Pi(z,zp)*C1p^(-gam);
          end
          lhs=R2*lhs; rhs=R1*(1+(dr*a-s)/cc1)^(-gam)*rhs;
          mg=lhs/rhs-1; if mg<0, nf=nf+1; end
          if mg<worst, worst=mg; wk=k+1; wa=a; wz=z; end
        end
      end
    end
    fprintf('   %.2f | %6.2f%% | %+9.4f | (%2d, %6.2f, %d) | %5.2f%%\n',phi,100*nf/nt,worst,wk,wa,wz,100*nT1/nt);
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
