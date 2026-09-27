% LEAD 2: the borrowing-constraint channel.  Household N has a stage-dependent loose limit
%   a' >= -f_k(R),  f_k = theta * NBL_k,  NBL_k = sum_{i<=k} y_min R^{-i}   (theta < 1 keeps c > 0).
% Decompose, at a >= 0:  [g0(R2)-g0(R1)] = [gN(R2)-gN(R1)] + cross,  cross = (g0-gN)(R2) - (g0-gN)(R1).
% Measure (i) Theorem 1 for N, (ii) size/sign of cross vs the N response, (iii) StageSlack for N.
function nbl
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
[Pi,y]=tauchen(rho,sigma,nz);
r1=0.04; r2=0.06; R1=1+r1; R2=1+r2; dr=r2-r1;
for theta=[0.9 0.5]
 for gam=[2 3]
  [c1,f1,ag]=egmf(R1,beta,gam,y,Pi,J,theta); [c2,f2,~]=egmf(R2,beta,gam,y,Pi,J,theta);
  c01=egmf(R1,beta,gam,y,Pi,J,0); c02=egmf(R2,beta,gam,y,Pi,J,0);
  na=numel(ag); m1=y'+R1*ag; m2=y'+R2*ag;
  reach=zeros(J,1); a=0;
  for j=1:J-1, k=J-j; a=max(y(end)+R2*a-interp1(ag,c2{k+1}(:,end),a,'linear','extrap'),0); reach(j+1)=a; end
  nT=0; nTf=0; nTn=0; nTnf=0; wT=inf; nx=0; nxneg=0; nxflip=0; ratios=[]; nS=0; nSf=0; wS=inf; wSs=[0 0 0];
  for j=2:J-1
    k=J-j;                                  % age j: stage k+1 = J-j+1 today (index k+2), stage k tomorrow (index k+1)
    GN1=m1-c1{k+2}; GN2=m2-c2{k+2}; G01=m1-c01{k+2}; G02=m2-c02{k+2};
    for z=1:nz
      for i=1:na
        a=ag(i); if a>reach(j), break; end
        if a< -min(f1(k+2),f2(k+2)), continue; end     % infeasible for N at this stage
        dN=GN2(i,z)-GN1(i,z);
        if a>=0, nT=nT+1; nTf=nTf+(dN<-1e-9); wT=min(wT,dN); else, nTn=nTn+1; nTnf=nTnf+(dN<-1e-9); end
        if a>=0
          d0=G02(i,z)-G01(i,z); cross=d0-dN; nx=nx+1;
          if cross<-1e-9, nxneg=nxneg+1; if cross<-dN, nxflip=nxflip+1; end, end
          if dN>1e-6, ratios(end+1)=cross/dN; end
          % StageSlack for N at interior states
          cc1=c1{k+2}(i,z); b1=m1(i,z)-cc1;
          if b1>-f1(k+1)+1e-6
            Cp=zeros(nz,1); for zp=1:nz, Cp(zp)=interp1(ag,c1{k+1}(:,zp),b1,'linear','extrap'); end
            w=Pi(z,:)'; lhs=R2*(w'*((Cp+dr*b1).^(-gam)))*(1+dr*a/cc1)^gam; rhs=R1*(w'*(Cp.^(-gam)));
            mg=lhs/rhs-1; nS=nS+1; nSf=nSf+(mg<0); if mg<wS, wS=mg; wSs=[k+1 a z]; end
          end
        end
      end
    end
  end
  fprintf('theta=%.1f gamma=%d : Thm1(N) fails %5.2f%% at a>=0 (worst %+.4f), %5.2f%% at a<0 | cross<0 at %5.1f%% of states, flips sign at %d | cross/dN quantiles 10/50/90: %+.2f %+.2f %+.2f | StageSlack(N) fails %5.2f%%, worst %+.4f at (k=%d,a=%.2f,z=%d)\n',...
    theta,gam,100*nTf/nT,wT,100*nTnf/max(nTn,1),100*nxneg/nx,nxflip,quantile(ratios,0.1),quantile(ratios,0.5),quantile(ratios,0.9),100*nSf/nS,wS,wSs);
 end
end
end
function [c,f,ag]=egmf(R,beta,gam,y,Pi,J,theta)
% stage-dependent floor f(k+1) = theta*NBL_k ; c{k+1} = stage-k consumption on the common grid ag
nz=numel(y); ymin=min(y);
nbl=zeros(J,1); for k=1:J-1, nbl(k+1)=nbl(k)/R+ymin/R; end
f=theta*nbl;                                   % f(k+1) = limit on a' chosen at stage k+1 (= -f applies to a' at stage k... )
% convention: at stage k+1 (index k+2) the choice a' must satisfy a' >= -f(k+1) where f(k+1)=theta*NBL_k
fmax=max(f); na=500; ag=[-fmax+[0; exp(linspace(log(1e-4),log(300+fmax),na-1))']];
m=y'+R*ag; c=cell(J,1); c{1}=max(m,1e-12);
for k=1:J-1
  lo=-f(k+1); ia=find(ag>=lo);                 % feasible a' grid
  up=c{k}(ia,:).^(-gam); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gam); mend=cend+ag(ia); cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z)-lo;   % constrained: a' = lo
  end
  c{k+1}=max(min(cn,m-lo),1e-12);
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
