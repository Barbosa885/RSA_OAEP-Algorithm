'''
Segurança Computacional - T3 - RSA-OAEP

Integrantes:
                David Herbert de Souza Brito - 200057405
                Gustavo Barbosa de Almeida - 202037589
                Isabelle Alex dos Santos Basílio Caldas - 170105636
'''

import os
import random
import hashlib as hash_lib
import base64
from math import ceil


class ChaveRSA():
    ''' Determina métodos que serão utilizados para geração das chaves '''

    def __init__(self):
        pass

    def gerar_chave(self, p, q, e):
        '''Cria chave pública(e, n) e a chave privada
        (d, n)
        input:
            p, q = números primos grandes, inteiros
            e = expoente da chave pública, inteiro
        output:
            chave pública, chave privada
        '''
        assert self.eh_primo(p, 7) and self.eh_primo(q, 7)
        assert p != q
        n = p * q
        phi = (p - 1) * (q - 1)
        if e is not None:
            assert self.mdc(phi, e) == 1
        else:
            while True:
                e = random.randrange(1, phi)
                if self.mdc(e, phi) == 1:
                    break
        d = self.modulo_inverso(e, phi)
        return ((e, n), (d, n))

    def mdc(self, a, b):
        '''Calcula o MDC (maior divisor comum) de a e b usando o algoritmo euclidiano
        input:
            a, b = dois inteiros desejados
        output:
            maior divisor comum entre "a" e "b"
        '''
        while b != 0:
            a, b = b, a % b
        return a

    def euclid_extendido(self, a, b):
        '''
        Usa o algoritmo euclidiano extendido para calcular os números x e y para os quais:

            a * x + b * y = euclid(a, b)

        input:
            a, b = dois inteiros desejados
        output:
            y, x, q = valores correspondentes, inteiros
        '''

        if b == 0:
            return 1, 0, a
        else:
            x, y, q = self.euclid_extendido(b, a % b)
            return y, x - (a // b) * y, q

    def modulo_inverso(self, a, b):
        '''
        Calcula o módulo inverso

        input:
            a, b = dois inteiros desejados
        output:    
            o módulo inverso ou None
        '''
        x, y, q = self.euclid_extendido(a, b)
        if q != 1:
            return None
        else:
            return x % b

    def teste_miller(self, d, n):
        '''
        Executa o teste de primalidade de Miller-Rabin
        input:
            d = número primo d para o qual n-1 = 2*d^r
            n = inteiro que se deseja testar
        output:
            booleano indicando a primalidade de n
        '''
        a = 2 + random.randint(1, n - 4)

        x = pow(a, d, n)
        if (x == 1 or x == n - 1):
            return True
        while (d != n - 1):
            x = (x * x) % n
            d *= 2

            if (x == 1):
                return False
            if (x == n - 1):
                return True

        return False

    def eh_primo(self, n, k):
        '''
        Determina se o número n é primo

        input:
            n = inteiro desejado
            k = número de vezes que o número será testado, inteiro
        output:    
            Booleano indicando a primalidade de n
        '''

        if (n <= 1 or n == 4):
            return False
        if (n <= 3):
            return True

        d = n - 1
        while (d % 2 == 0):
            d //= 2
        for i in range(k):
            if (self.teste_miller(d, n) == False):
                return False

        return True


class FerramentasCripto():
    ''' 
        Determina métodos que serão utilizados no processo de encriptação e decriptação
    '''

    def __init__(self):
        ''' hlen = comprimento do hash, inteiro'''
        self.tam_hash = len(self.sha3(b''))

    def os2ip(self, x):
        '''
        Converte o bytearray desejado para inteiro

        input:  
            x = bytearray
        output: 
            inteiro correspondente não negativo
        '''
        return int.from_bytes(x, byteorder='big')

    def i2osp(self, x, l):
        '''
        Converte um inteiro não negativo em bytearray

        input:
            x = inteiro não negativo
            l = comprimento desejado em bytes
        output:
            bytearray correspondente
        '''
        return x.to_bytes(l, "big")

    def sha3(self, m):
        '''
        Encripta uma mensagem com sha3

        input:
            m = mensagem para ser hasheada, bytearray
        output:
            hash correspondente, bytearray
        '''
        hasher = hash_lib.sha3_512()
        hasher.update(m)
        return hasher.digest()

    def mgf(self, z, l):
        '''
        Gera a máscara que será utilizada na encriptação
        input:
            z = seed, bytearray
            l = número de bytes desejado, inteiro
        output:
            T = máscara resultante, bytearray
        '''
        assert l < (2**32)

        T = b""

        for i in range(ceil(l / self.tam_hash)):
            C = self.i2osp(i, 4)
            T += self.sha3(z + C)
        return T[:l]

    def xor_bitwise(self, data, mask):
        '''
        Aplica a máscara "mask" em um bytearray "data" através de um xor bit a bit

        input:
            data = data, bytearray
            mask = máscara, bytearray 
        output:
            T = bytearray com a máscara aplicada, bytearray
        '''
        mascarado = b''
        ldata = len(data)
        lmask = len(mask)
        for i in range(max(ldata, lmask)):
            if i < ldata and i < lmask:
                mascarado += (data[i] ^ mask[i]).to_bytes(1, byteorder='big')
            elif i < ldata:
                mascarado += data[i].to_bytes(1, byteorder='big')
            else:
                break
        return mascarado


class Encriptar(FerramentasCripto):
    '''Define métodos que serão utilizados para a encriptação RSA-OAEP'''

    def oaep_codificar(self, mensagem, k, rotulo=b''):
        '''
        Usa o algoritmo oaep para encriptar a mensagem "mensagem"

        input:
            mensagem = mensagem, bytearray
            k = tamanho da chave pública em bytes, inteiro
        output:
            mensagem encriptada, bytearray 
        '''
        tam_mensagem = len(mensagem)
        hash_l = self.sha3(rotulo)
        ps = b'\x00' * (k - tam_mensagem - 2 * self.tam_hash - 2)
        db = hash_l + ps + b'\x01' + mensagem
        seed = os.urandom(self.tam_hash)
        db_mascara = self.mgf(seed, k - self.tam_hash - 1)
        db_mascarado = self.xor_bitwise(db, db_mascara)
        seed_mascara = self.mgf(db_mascarado, self.tam_hash)
        seed_mascarado = self.xor_bitwise(seed, seed_mascara)
        return b'\x00' + seed_mascarado + db_mascarado

    def encriptar_rsa_oaep(self, mensagem, chave_publica):
        '''
        Encripta a mensagem "mensagem" utilizando o algoritmo RSA modelo OAEP

        input:
            mensagem = mensagem, bytearray
            chave_publica = chave pública, bytearray
        output:
            mensagem encriptada, bytearray
            assinatura da mensagem, bytearray
        '''
        k = ceil((chave_publica[1]).bit_length() / 8)

        assert len(mensagem) <= k - self.tam_hash - 2

        e, n = chave_publica
        c = self.oaep_codificar(mensagem, k)
        c = pow(self.os2ip(c), e, n)

        return self.i2osp(c, k)


class Desencriptar(FerramentasCripto):
    '''Define métodos que serão utilizados para a decriptação RSA-OAEP'''

    def oaep_decodificar(self, c, k, rotulo=b''):
        '''EME-OAEP decoding
        Usa o algoritmo oaep para decriptar a mensagem "c"

         input:
            c = mensagem, bytearray
            k = tamanho da chave privada em bytes, inteiro
        output:
            mensagem decriptada, bytearray
        '''
        hash_l = self.sha3(rotulo)
        _, seed_mascarada, db_mascarado = c[:1], c[1:1 +
                                                  self.tam_hash], c[1 + self.tam_hash:]
        seed_mascara = self.mgf(db_mascarado, self.tam_hash)
        seed = self.xor_bitwise(seed_mascarada, seed_mascara)
        db_mascara = self.mgf(seed, k - self.tam_hash - 1)
        db = self.xor_bitwise(db_mascarado, db_mascara)
        _hash_l = db[:self.tam_hash]
        assert hash_l == _hash_l
        i = self.tam_hash
        while i < len(db):
            if db[i] == 0:
                i += 1
                continue
            elif db[i] == 1:
                i += 1
                break
            else:
                raise Exception()
        mensagem = db[i:]
        return mensagem

    def desencriptar_rsa_oaep(self, c, chave_privada):
        '''Decrypt a cipher byte array with OAEP padding
        Decripta a mensagem "c" utilizando o algoritmo RSA modelo OAEP

        input:
            c = mensagem, bytearray
            chave_privada = chave privada, bytearray
        output:
            mensagem decriptada, bytearray
        '''
        k = ceil((chave_privada[1]).bit_length() / 8)
        assert len(c) == k
        assert k >= 2 * self.tam_hash + 2

        d, n = chave_privada
        mensagem = pow(self.os2ip(c), d, n)
        mensagem = self.i2osp(mensagem, k)

        return self.oaep_decodificar(mensagem, k)

class Receptor(ChaveRSA, Desencriptar):
    '''
    Responsável por receber a mensagem encriptada, decriptá-la e testá-la com a Assinatura
    '''

    def __init__(self, novaChave=True):
        '''Construtor da classe Receptor
        input:
            novaChave = indica se uma nova chave será gerada, booleano
        '''
        e = 0x010001

        if novaChave:
            print("Gerando chaves(0/2)...")
            p = 1
            while (not self.eh_primo(p, 7)):
                p = random.randint(2**1023, 2**1024)
            print("Gerando chaves(1/2)...")
            q = 1
            while (not self.eh_primo(q, 7)) or p == q:
                q = random.randint(2**1023, 2**1024)
            print("Gerando chaves(2/2)...")
            print("Geração completa!")
            # salvar nova chave
            print("Selecione um nome para o novo arquivo de chaves:\n")
            print(
                "Aviso: não usar caracteres especiais ou especificar a extensão do arquivo")
            print("Exemplo de entrada: >exemplo\n")
            nome = str(input(">"))
            self.nome = nome
            with open(nome + ".txt", "w+") as f:
                f.write(str(p) + "\n")
                f.write(str(q) + "\n")
        else:
            # usar chave antiga
            print("Digite o arquivo de chave que deseja utilizar\n")
            print(
                "Aviso: não usar caracteres especiais ou especificar a extensão do arquivo")
            print("Exemplo de entrada: >exemplo\n")
            nome = str(input(">"))
            self.nome = nome
            with open(nome + ".txt", "r") as f:
                if f:
                    p = int(f.readline())
                    q = int(f.readline())
        print("----------------Primos em hexadecimal----------------------")
        print("primo 1:", hex(p))
        print("primo 2:", hex(q))
        ChaveRSA.__init__(self)
        Desencriptar.__init__(self)
        self.chavePublica, self.chavePrivada = self.gerar_chave(p, q, e)
        print("---------------Chaves de criptação --------------")
        print("Chave pública:", self.chavePublica)
        print("Chave privada:\n\n", self.chavePrivada[0])

    def iniciarConexao(self):
        '''Inicia a conexão entre sender e receiver instanciando o server'''
        self.servidor = [Servidor(self.chavePublica, self.nome)]
        return self.servidor

    def decriptarMensagem(self):
        '''Decripta a mensagem armazenada no server'''
        assinatura, mensagem = self.servidor[0].pegarMensagem()
        d, n = self.servidor[0].chavePublicaRemetente
        mensagemDecriptada = self.desencriptar_rsa_oaep(mensagem, self.chavePrivada)

        s = self.i2osp(pow(self.os2ip(assinatura), d, n), 64)

        if(s == self.sha3(mensagemDecriptada)):
            print("Mensagem recebida com sucesso!!")
            print("Mensagem decriptada:", mensagemDecriptada.decode("utf-8"), "\n")
            print("---------------------------------------------")
        else:
            print("ERRO: Assinatura da mensagem incompatível.")


class Servidor():
    '''
    Determina a comunicação entre Sender e Receiver, garantindo acesso apenas à mensagem encriptada e à chave pública de ambos
    '''

    def __init__(self, chavePublicaReceptor, nome):
        '''Construtor da classe servidor'''
        self.chavePublicaReceptor = chavePublicaReceptor
        self.nome = nome

    def definirMensagem(self, assinatura, mensagemEncriptada):
        '''Grava a mensagem e a assinatura no .txt correspondente
        input: 
            assinatura, mensagemEncriptada = bytearrays
        '''
        self.mensagemEncriptada = mensagemEncriptada
        # print(assinatura)
        base64StringCodificada = base64.b64encode(mensagemEncriptada)
        base64StringSCodificada = base64.b64encode(assinatura)
        with open('mensagem' + self.nome + '.txt', 'w+') as f:
            print("Assinatura da mensagem:", base64StringSCodificada.decode('utf-8'))
            print("Mensagem encriptada: " +
                  base64StringCodificada.decode('utf-8')+"\n")
            f.write(base64StringSCodificada.decode('utf-8')+"\n")
            f.write(base64StringCodificada.decode('utf-8'))

    def pegarMensagem(self):
        '''Lê a mensagem gravada no txt correspondente
        output:
            assinatura, mensagem = assinatura e mensagem encriptada, bytearray
        '''
        with open('mensagem'+self.nome+'.txt', 'r') as f:
            if not f:
                print('ERRO: Arquivo de mensagem inexistente')
                return None
            else:
                m = f.readline()
                assinatura = base64.b64decode(m.encode("utf-8"))
                m = f.readline()
                mensagem = base64.b64decode(m.encode("utf-8"))
                return assinatura, mensagem

    # sets e gets para valores específicos
    def definirChavePublicaRemetente(self, chavePublicaRemetente): self.chavePublicaRemetente = chavePublicaRemetente
    def pegar_e(self): return self.e
    def pegar_n(self): return self.n


class Remetente(Encriptar, ChaveRSA):
    '''
    Responsável por encriptar a mensagem e a assinatura e enviá-las ao servidor
    '''

    def __init__(self, servidor):
        '''Construtor da classe remetente
        input:
            servidor = ponteiro para acessar o Servidor instanciado pela classe Receptor, lista com um objeto servidor instanciado, [Servidor]
        '''
        self.servidor = servidor
        '''p e q são primos grandes constantes que criarão a chave privada e pública do servidor para ser utilizada na assinatura'''
        e = 0x010001
        p = 97962796904280205888084811562964488190962410580438986602772964729043975540681631621472675024214515491932452297662896068200477857556195577301442157032294788012249197257876876439702478794510158895189770668271842399008851096255918615617091562859396319516675952918545998915860198564813082383638996319228274522199
        q = 179254215470244753801670806037636828877229308262366906189173021362198522014648917380717440609954562680936353318826278100387818010717325117950339338189158413352932790197268235586554618256304106325838871838101470934772890880184013442978003681873677779889327057473152412199836756580050573796447220026994889221457
        super().__init__()
        self.chavePublica, self.chavePrivada = self.gerar_chave(p, q, e)
        self.servidor[0].definirChavePublicaRemetente(self.chavePublica)

    def criptMensagem(self, mensagem):
        '''Encripta a mensagem desejada
        input:
            mensagem = mensagem desejada, string
        '''
        assinatura = self.criarAssinatura(mensagem)
        mensagemEncriptada = self.encriptar_rsa_oaep(mensagem.encode('utf-8'), self.servidor[0].chavePublicaReceptor)
        self.servidor[0].definirMensagem(assinatura, mensagemEncriptada)

    def criarAssinatura(self, mensagem):
        '''Gera a assinatura da mensagem
        input:
            mensagem = mensagem desejada, string
        output: 
            s = assinatura da mensagem, bytearray 
        '''
        e, n = self.chavePrivada
        s = self.i2osp(
            pow(self.os2ip(self.sha3(mensagem.encode("utf-8"))), e, n), 256)

        return s


def limparConsole():
    '''
    Função que limpa o terminal
    '''
    comando = 'clear'
    if os.name in ('nt', 'dos'):  # If Machine is running on Windows, use cls
        comando = 'cls'
    os.system(comando)


def main():
    interfacePrincipal = "Bem-vindo ao encriptador e decriptador de RSA-OAEP!\n\n"
    interfacePrincipal += "\tEste programa implementa um algoritmo RSA tipo OAEP e replica como seria uma aplicação deste algoritmo na comunicação em um servidor utilizando orientação a objetos\n\n"
    interfacePrincipal += "Selecione uma das opções:\n"
    interfacePrincipal += "\t1 - Encriptar uma mensagem\n"
    interfacePrincipal += "\t2 - Decriptar uma mensagem\n"
    interfacePrincipal += "\tS - Sair\n\n"
    opcaoPrincipal = None
    while not (opcaoPrincipal == 's' or opcaoPrincipal == 'S'):
        opcaoPrincipal = str(input(interfacePrincipal + ">"))
        if opcaoPrincipal == '1':
            limparConsole()
            print("Deseja utilizar uma chave de sessão já definida anteriormente?(y/n)")
            if(str(input(">")) == "n"):
                receptor = Receptor(novaChave=True)
            else:
                avisoInterface = "Aviso: a mensagem encriptada com essa chave anteriormente será sobrescrita, desejas continuar? (y/n) "
                if(str(input(avisoInterface + ">")) != "y"):
                    continue
                limparConsole()
                receptor = Receptor(novaChave=False)
            print("Conexão entre remetente e receptor criada")
            remetente = Remetente(receptor.iniciarConexao())

            interfaceEncriptacao = "Defina qual mensagem deve ser encriptada:\n"
            remetente.criptMensagem(str(input(interfaceEncriptacao + ">")))
        elif opcaoPrincipal == '2':
            try:
                receptor = Receptor(novaChave=False)
            except:
                limparConsole()
                print('ERRO: Arquivo de chave inexistente\n')
                continue
            remetente = Remetente(receptor.iniciarConexao())
            try:
                receptor.decriptarMensagem()
            except AssertionError:
                print("ERRO: chave incompatível")
            except FileNotFoundError:
                print("ERRO: arquivo de mensagem inexistente")
        elif not (opcaoPrincipal == 's' or opcaoPrincipal == 'S'):
            limparConsole()
            print("ERRO: Opção inexistente\n\n")


if __name__ == "__main__":
  main()

