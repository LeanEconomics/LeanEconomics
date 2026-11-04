% Explicit lower capital clamp of KrusellSmith/CobbDouglasCapital.lean, evaluated at Krusell-Smith
% style calibrations. Every constant follows the Lean definitions exactly:
%   wageConst  D  = (1-alpha)*zLo*labHi^(-alpha)*labLo/2
%   eulerConst C1 = (beta*pi*alpha*zLo*labLo^(1-alpha))^(-1/gamma)
%   outputConst C2 = zHi*labHi^(1-alpha)
%   LowerClampOK k: k<=1, k*effHi<=assetCap*labLo/2, k^(1-alpha)<D/2, C1*(1+C2)*k^((1-alpha)/gamma)<D/2
%   exists_capLo threshold k0 = min(1, assetCap*labLo/(2*effHi), t/2, u/2),
%     t = (D/2)^(1/(1-alpha)), u = (D/(2*C1*(1+C2)))^(gamma/(1-alpha))
% kSup = min(1, assetCap*labLo/(2*effHi), t, u) is the supremum of the k satisfying LowerClampOK.
% If capLo <= k0, the clamp never binds in any CRRA equilibrium starting from mean assets >= capLo
% (crra_capital_mem), with labour clamp [labLo,labHi] = [effLo,effHi] and capHi >= assetCap.

diary('capLoCRRACobbDouglas.txt'); diary on

% Krusell-Smith (1998) quarterly calibration; aggregate shocks persist 8 quarters on average
CalQ.name='quarterly'; CalQ.beta=0.99; CalQ.delta=0.025;
% Annual version
CalA.name='annual'; CalA.beta=0.96; CalA.delta=0.1;
Cals={CalQ,CalA};

alpha=0.36; zLo=0.99; zHi=1.01;
piRepeat=0.875;              % minimum probability that the aggregate shock repeats
effHi=1;                     % employed efficiency
effLoVec=[0.07,0.15,0.25];   % unemployed efficiency (must be positive in the theorem)
gammaVec=[1,2,5];

for cc=1:length(Cals)
    Cal=Cals{cc};
    % complete-markets steady-state capital at labour 1, for scale
    Kcm=(alpha*zLo/(1/Cal.beta-1+Cal.delta))^(1/(1-alpha));
    assetCap=10*Kcm;
    fprintf('\n=== %s: beta=%5.3f, delta=%5.3f, alpha=%4.2f, z in [%4.2f,%4.2f], pi=%5.3f ===\n', ...
        Cal.name,Cal.beta,Cal.delta,alpha,zLo,zHi,piRepeat)
    fprintf('Complete-markets capital (L=1): %8.4f, assetCap = 10x that = %8.4f\n',Kcm,assetCap)
    fprintf('%6s %6s %11s %11s %11s %11s %11s %9s %s\n','effLo','gamma','D','C1','C2','k0','kSup','k0/Kcm','binding')
    for effLo=effLoVec
        labLo=effLo; labHi=effHi;
        for gamma=gammaVec
            D=(1-alpha)*zLo*labHi^(-alpha)*labLo/2;
            C1=(Cal.beta*piRepeat*alpha*zLo*labLo^(1-alpha))^(-1/gamma);
            C2=zHi*labHi^(1-alpha);
            bounds=[1, assetCap*labLo/(2*effHi), (D/2)^(1/(1-alpha)), (D/(2*C1*(1+C2)))^(gamma/(1-alpha))];
            names={'k<=1','cap','wage','euler'};
            k0=min([bounds(1:2), bounds(3:4)/2]);
            [kSup,ind]=min(bounds);
            % check LowerClampOK at k0 directly
            ok = k0<=1 && k0*effHi<=assetCap*labLo/2 && k0^(1-alpha)<D/2 && C1*(1+C2)*k0^((1-alpha)/gamma)<D/2;
            if ~ok
                error('LowerClampOK fails at k0: formula check')
            end
            fprintf('%6.2f %6.1f %11.4e %11.4e %11.4e %11.4e %11.4e %9.2e %s\n',effLo,gamma,D,C1,C2,k0,kSup,k0/Kcm,names{ind})
        end
    end
end

% Sensitivity to the repeat probability, quarterly, effLo=0.15
fprintf('\n=== Sensitivity to pi (quarterly, effLo=0.15) ===\n')
fprintf('%6s %6s %11s %9s\n','pi','gamma','k0','k0/Kcm')
Cal=CalQ; Kcm=(alpha*zLo/(1/Cal.beta-1+Cal.delta))^(1/(1-alpha)); assetCap=10*Kcm;
labLo=0.15; labHi=effHi;
for piR=[0.5,0.875,0.95]
    for gamma=gammaVec
        D=(1-alpha)*zLo*labHi^(-alpha)*labLo/2;
        C1=(Cal.beta*piR*alpha*zLo*labLo^(1-alpha))^(-1/gamma);
        C2=zHi*labHi^(1-alpha);
        k0=min([1, assetCap*labLo/(2*effHi), (D/2)^(1/(1-alpha))/2, (D/(2*C1*(1+C2)))^(gamma/(1-alpha))/2]);
        fprintf('%6.3f %6.1f %11.4e %9.2e\n',piR,gamma,k0,k0/Kcm)
    end
end

fprintf('\ncapLoCRRACobbDouglas finished\n')
diary off
